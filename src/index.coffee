require 'fy/codegen'
Type = require 'type'

module = @
@bin_op_name_map =
  ADD : '+'
  SUB : '-'
  MUL : '*'
  DIV : '/'
  MOD : '%'
  
  BIT_AND : '&'
  BIT_OR  : '|'
  BIT_XOR : '^'
  
  BOOL_AND : '&&'
  BOOL_OR  : '||'
  BOOL_XOR : '^'
  
  SHR : '>>'
  SHL : '<<'
  LSR : '>>>'
  
  # ASSIGN : '='
  
  ADD : '+'
  SUB : '-'
  MUL : '*'
  DIV : '/'
  MOD : '%'
  
  BIT_AND : '&'
  BIT_OR  : '|'
  BIT_XOR : '^'
  
  BOOL_AND : '&&'
  BOOL_OR  : '||'
  BOOL_XOR : '^'
  
  SHR : '>>'
  SHL : '<<'
  LSR : '>>>'
  
  EQ : '=='
  NE : '!='
  GT : '>'
  LT : '<'
  GTE: '>='
  LTE: '<='

@bin_op_name_cb_map =
  POW           : (a, b)-> "Math.pow(#{a}, #{b})"
  ASSIGN        : (a, b)-> "#{a} = #{b}"
  ASS_ADD       : (a, b)-> "#{a} += #{b}"
  ASS_SUB       : (a, b)-> "#{a} -= #{b}"
  ASS_MUL       : (a, b)-> "#{a} *= #{b}"
  ASS_DIV       : (a, b)-> "#{a} /= #{b}"
  ASS_MOD       : (a, b)-> "#{a} %= #{b}"
  ASS_BIT_AND   : (a, b)-> "#{a} &= #{b}"
  ASS_BIT_OR    : (a, b)-> "#{a} |= #{b}"
  ASS_BIT_XOR   : (a, b)-> "#{a} ^= #{b}"
  ASS_BOOL_AND  : (a, b)-> "#{a} &= #{b}"
  ASS_BOOL_OR   : (a, b)-> "#{a} |= #{b}"
  ASS_BOOL_XOR  : (a, b)-> "#{a} ^= #{b}"
  ASS_SHR       : (a, b)-> "#{a} >>= #{b}"
  ASS_SHL       : (a, b)-> "#{a} <<= #{b}"
  ASS_LSR       : (a, b)-> "#{a} >>= #{b}" # minor flaw

# @pow = (a, b, ta, tb) ->
#   if tb == "int"
#     if ta == "int"
#       "(#{a} as i32).pow(#{b} as u32)"
#     else if ta == "float"
#       "(#{a} as f32).powi(#{b})"
#     else
#       throw new Error "Invalid base type for POW: #{ta}"
#   else if tb == "float"
#     if ta == "int" or ta == "float"
#       "(#{a} as f32).powf(#{b})"
#     else
#       throw new Error "Invalid base type for POW: #{ta}"
#   else
#     throw new Error "Invalid exponent type for POW: #{tb}"

# @ass_pow = (a, b, ta, tb) ->
#   "{#{a} = #{module.pow a, b, ta, tb}; a}"

@un_op_name_cb_map =
  INC_RET : (a)->"{#{a} += 1; #{a}}"
  RET_INC : (a)->"{let __copy_#{a} = #{a}; #{a} += 1; __copy_#{a}}"
  DEC_RET : (a)->"{#{a} -= 1; #{a}}"
  RET_DEC : (a)->"{let __copy_#{a} = #{a}; #{a} -= 1; __copy_#{a}}"
  BOOL_NOT: (a)->"!(#{a})"
  BIT_NOT : (a)->"!(#{a})"
  MINUS   : (a)->"-(#{a})"
  PLUS    : (a)->"Float.parseFloat(#{a})"
  IS_NOT_NULL: (a)->"(#{a} != null)"

recast_hash =
  'bool'  : 'boolean'
  'int'   : 'int'
  'float' : 'float'
  'string': 'String'
  'array' : 'ArrayList'

type_recast = (t)->
  t = t.clone()
  t.main = recast_hash[t.main] or t.main
  if t.main == 'hash_int'
    t.main = 'HashMap'
    t.nest_list.unshift new Type 'Integer'
  # if !t.main = recast_hash[t.main]    # За такий код потрібно яйця відкручувати. Хоч би дужки поставив.
  #   throw new Error "Can't recast #{t.main} in Rust"
  for field,k in t.nest_list
    t.nest_list[k] = type_recast field
  for k,field in t.field_hash
    t.field_hash[k] = type_recast field
  t

class @Gen_context
  in_class : false
  var_uid : 0
  mk_nest : ()->
    t = new module.Gen_context
    t

@gen = gen = (ast, ctx = new module.Gen_context)->
  switch ast.constructor.name
    # ###################################################################################################
    #    expr
    # ###################################################################################################
    when "Const"
      switch ast.type.main
        when 'bool', 'int'
          ast.val
        when 'float'
          "#{ast.val}f"
        when 'string'
          JSON.stringify ast.val
    
    when "Array_init"
      jl = []
      for v in ast.list
        jl.push gen v, ctx
      "[#{jl.join ', '}]"
    
    when "Hash_init", "Struct_init"
      jl = []
      for k,v of ast.hash
        jl.push "#{JSON.stringify k}: #{gen v, ctx}"
      "{#{jl.join ', '}}"
    
    when "Var"
      if ast.name == 'this'
        'this'
      else
        ast.name
    
    when "Bin_op"
      _a = gen ast.a, ctx
      _b = gen ast.b, ctx
      ta = ast.a.type?.main
      tb = ast.b.type?.main
      # if ast.op == "POW"
      #   return module.pow _a, _b, ta, tb
      # if ast.op == "ASS_POW"
      #   return module.ass_pow _a, _b, ta, tb
      # if ast.type?.main == "float"
      #   if ta == "int"
      #     _a += " as f32"
      #   if tb == "int"
      #     _b += " as f32"
      ret = ""
      loop
        if ast.op == 'INDEX_ACCESS'
          ret = switch ta
            when "array"
              "(#{_a}).get(#{_b})"
            else
              throw new Error "can't compile INDEX_ACCESS for '#{ast.a.type}'"
          break
        ret = if op = module.bin_op_name_map[ast.op]
          "(#{_a} #{op} #{_b})"
        else
          module.bin_op_name_cb_map[ast.op](_a, _b)
        break
      ret
    
    when "Un_op"
      module.un_op_name_cb_map[ast.op] gen ast.a, ctx
    
    when "Field_access"
      "#{gen(ast.t, ctx)}.#{ast.name}"
    
    when "Fn_call"
      ret = ""
      if ast.fn.constructor.name == 'Field_access'
        t = ast.fn.t
        ret = switch t.type.main
          # TODO array
          # TODO hash
          when 'array'
            switch ast.fn.name
              when 'new'
                "#{gen t, ctx} = new #{type_recast ast.fn.t.type}()"
              when 'push'
                "#{gen t, ctx}.add(#{gen ast.arg_list[0], ctx})"
          
          when 'hash_int'
            switch ast.fn.name
              when 'new'
                "#{gen t, ctx} = new #{type_recast ast.fn.t.type}()"
              when 'add'
                "#{gen t, ctx}.put(#{gen ast.arg_list[0], ctx}, #{gen ast.arg_list[1], ctx})"
              when 'remove_idx'
                "#{gen t, ctx}.remove(#{gen ast.arg_list[0], ctx})"
              when 'idx'
                "#{gen t, ctx}.get(#{gen ast.arg_list[0], ctx})"
              else
                throw new Error "unsupported #{t.type.main} method '#{ast.fn.name}'"
          else
            if ast.fn.name == 'new'
              "#{gen t, ctx} = new #{t.type.main}()"
            else
              ""
      if !ret
        jl = []
        for v in ast.arg_list
          jl.push gen v, ctx
        ret = "#{gen ast.fn, ctx}(#{jl.join ', '})"
      ret
    # ###################################################################################################
    #    stmt
    # ###################################################################################################
    when "Scope"
      jl = []
      for v in ast.list
        t = gen v, ctx
        jl.push t if t != ''
      jl.join ";\n"
    
    when "If"
      cond = gen ast.cond, ctx
      t = gen ast.t, ctx
      f = gen ast.f, ctx
      if f == ''
        """
        if (#{cond}) {
          #{make_tab t, '  '};
        }
        """
      else if t == ''
        """
        if (!(#{cond})) {
          #{make_tab f, '  '};
        }
        """
      else
        """
        if (#{cond}) {
          #{make_tab t, '  '};
        } else {
          #{make_tab f, '  '};
        }
        """
    
    when "Switch"
      jl = []
      for k,v of ast.hash
        if ast.cond.type.main == 'string'
          k = JSON.stringify k
        jl.push """
        case #{k}:
          #{make_tab gen(v, ctx), '  '};
          break;
        """
      
      if "" != f = gen ast.f, ctx
        jl.push """
        default:
          #{make_tab f, '  '};
          break;
        """
      
      """
      switch (#{gen ast.cond, ctx}) {
        #{join_list jl, '  '}
      }
      """
    
    when "Loop"
      """
      while (true) {
        #{make_tab gen(ast.scope, ctx), '  '};
      }
      """
    
    when "While"
      """
      while (#{gen ast.cond, ctx}) {
        #{make_tab gen(ast.scope, ctx), '  '};
      }
      """
    
    when "Break"
      "break"
    
    when "Continue"
      "continue"
    
    when "For_range"
      aux_step = "++"
      if ast.step
        aux_step = " += #{gen ast.step, ctx}"
      ranger = if ast.exclusive then "<" else "<="
      i = gen ast.i, ctx
      """
      for (#{i} = #{gen ast.a, ctx}; #{i} #{ranger} #{gen ast.b, ctx}; #{i}#{aux_step}) {
        #{make_tab gen(ast.scope, ctx), '  '};
      }
      """
      # for #{gen ast.i, ctx} in [#{gen ast.a, ctx} #{ranger} #{gen ast.b, ctx}]#{aux_step}
    
    when "For_col"
      switch ast.t.type.main
        when 'array'
          uid = ctx.var_uid++
          if ast.v
            value = gen ast.v, ctx
          else
            value = "_v_#{uid}"
          
          aux_init = ""
          aux_incr = ""
          if ast.k
            iterator = "#{gen ast.k, ctx}"
            aux_init = "#{iterator} = -1;"
            aux_incr = "#{iterator}++;"
          """
          #{aux_init}
          for(#{type_recast ast.t.type.nest_list[0]} _#{value} : #{gen ast.t, ctx}) {
            #{aux_incr}
            #{value} = _#{value};
            #{make_tab gen(ast.scope, ctx), '  '};
          }
          """
        when 'hash'
          throw new Error "NOT IMPLEMENTED"
          # if ast.k
          #   aux_k = gen ast.k, ctx
          # else
          #   aux_k = "_skip"
          # 
          # aux_v = ""
          # if ast.v
          #   aux_v = ",#{gen ast.v, ctx}"
          # """
          # for #{aux_k}#{aux_v} of #{gen ast.t, ctx}
          #   #{make_tab gen(ast.scope, ctx), '  '};
          # """
        when 'hash_int'
          uid = ctx.var_uid++
          pair = "_pair_#{uid}"
          
          aux_k = ""
          aux_v = ""
          if ast.k
            aux_k = "#{gen ast.k, ctx} = #{pair}.getKey();"
          if ast.v
            aux_v = "#{gen ast.v, ctx} = #{pair}.getValue();"
          
          """
          for(Map.Entry<Integer, #{type_recast ast.t.type.nest_list[0]}> #{pair} : #{gen ast.t, ctx}.entrySet()) {
            #{aux_k}
            #{aux_v}
            #{make_tab gen(ast.scope, ctx), '  '};
          }
          """
      
        else
          throw new Error "unimplemented For_col '#{ast.t.type}'"
    
    when "Ret"
      aux = ""
      if ast.t
        aux = " (#{gen ast.t, ctx})"
      "return#{aux}"
    
    when "Try"
      """
      try
        #{make_tab gen(ast.t, ctx), '  '}
      catch #{ast.exception_var_name}
        #{make_tab gen(ast.c, ctx), '  '}
      """
    
    when "Throw"
      "panic!(#{gen ast.t, ctx})"
    
    when "Var_decl"
      "#{type_recast ast.type} #{ast.name}"
    
    when "Class_decl"
      ctx_nest = ctx.mk_nest()
      ctx_nest.in_class = true
      """
      class #{ast.name} {
        #{make_tab gen(ast.scope, ctx_nest), '  '};
      }
      """
    
    when "Fn_decl"
      arg_list = ast.arg_name_list
      sgnt_list = ast.type.nest_list
      sgnt_string = "("
      for t, i in sgnt_list[1..]
        sgnt_string += ", " if i != 0
        sgnt_string += "#{type_recast t} #{arg_list[i]}"
      sgnt_string += ")"
      """
      public #{type_recast sgnt_list[0]} #{ast.name}#{sgnt_string} {
        #{make_tab gen(ast.scope, ctx), '  '}#{if ast.scope.list.length then ';' else ''}
      }
      """
    