require 'fy/codegen'

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
  
  BOOL_AND : '&'
  BOOL_OR  : '|'
  BOOL_XOR : '^'
  
  SHR : '>>'
  SHL : '<<'
  LSR : '>>' # minor flaw
  
  ASSIGN : '='
  
  EQ : '=='
  NE : '!='
  GT : '>'
  LT : '<'
  GTE: '>='
  LTE: '<='

@bin_op_name_cb_map =
  ASS_ADD       : (a, b)-> "{#{a} += #{b}; #{a}}"
  ASS_SUB       : (a, b)-> "{#{a} -= #{b}; #{a}}"
  ASS_MUL       : (a, b)-> "{#{a} *= #{b}; #{a}}"
  ASS_DIV       : (a, b)-> "{#{a} /= #{b}; #{a}}"
  ASS_MOD       : (a, b)-> "{#{a} %= #{b}; #{a}}"
  ASS_BIT_AND   : (a, b)-> "{#{a} &= #{b}; #{a}}"
  ASS_BIT_OR    : (a, b)-> "{#{a} |= #{b}; #{a}}"
  ASS_BIT_XOR   : (a, b)-> "{#{a} ^= #{b}; #{a}}"
  ASS_BOOL_AND  : (a, b)-> "{#{a} &= #{b}; #{a}}"
  ASS_BOOL_OR   : (a, b)-> "{#{a} |= #{b}; #{a}}"
  ASS_BOOL_XOR  : (a, b)-> "{#{a} ^= #{b}; #{a}}"
  ASS_SHR       : (a, b)-> "{#{a} >>= #{b}; #{a}}"
  ASS_SHL       : (a, b)-> "{#{a} <<= #{b}; #{a}}"
  ASS_LSR       : (a, b)-> "{#{a} >>= #{b}; #{a}}" # minor flaw

@pow = (a, b, ta, tb) ->
  if tb == "int"
    if ta == "int"
      "(#{a} as i32).pow(#{b} as u32)"
    else if ta == "float"
      "(#{a} as f32).powi(#{b})"
    else
      throw new Error "Invalid base type for POW: #{ta}"
  else if tb == "float"
    if ta == "int" or ta == "float"
      "(#{a} as f32).powf(#{b})"
    else
      throw new Error "Invalid base type for POW: #{ta}"
  else
    throw new Error "Invalid exponent type for POW: #{tb}"

@ass_pow = (a, b, ta, tb) ->
  "{#{a} = #{module.pow a, b, ta, tb}; a}"

@un_op_name_cb_map =
  INC_RET : (a)->"{#{a} += 1; #{a}}"
  RET_INC : (a)->"{let __copy_#{a} = #{a}; #{a} += 1; __copy_#{a}}"
  DEC_RET : (a)->"{#{a} -= 1; #{a}}"
  RET_DEC : (a)->"{let __copy_#{a} = #{a}; #{a} -= 1; __copy_#{a}}"
  BOOL_NOT: (a)->"!(#{a})"
  BIT_NOT : (a)->"!(#{a})"
  MINUS   : (a)->"-(#{a})"
  PLUS    : (a)->"#{a}.parse::<f32>().unwrap()"

recast_hash =
  'bool'  : 'bool'
  'int'   : 'i32'
  'float' : 'f32'
  'string': '&str'
  'array' : 'Vec'

type_recast = (t)->
  t = t.clone()
  if !t.main = recast_hash[t.main]    # За такий код потрібно яйця відкручувати. Хоч би дужки поставив.
    throw new Error "Can't recast #{t.main} in Rust"
  for field,k in t.nest_list
    t.nest_list[k] = type_recast field
  for k,field in t.field_hash
    t.field_hash[k] = type_recast field
  t

class @Gen_context
  in_class : false
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
        when 'bool', 'int', 'float'
          ast.val
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
        'self'
      else
        ast.name
    
    when "Bin_op"
      _a = gen ast.a, ctx
      _b = gen ast.b, ctx
      ta = ast.a.type?.main
      tb = ast.b.type?.main
      if ast.op == "POW"
        return module.pow _a, _b, ta, tb
      if ast.op == "ASS_POW"
        return module.ass_pow _a, _b, ta, tb
      if ast.type?.main == "float"
        if ta == "int"
          _a += " as f32"
        if tb == "int"
          _b += " as f32"
      if op = module.bin_op_name_map[ast.op]
        "(#{_a} #{op} #{_b})"
      else
        module.bin_op_name_cb_map[ast.op](_a, _b)
    
    when "Un_op"
      module.un_op_name_cb_map[ast.op] gen ast.a, ctx
    
    when "Field_access"
      "(#{gen(ast.t, ctx)}).#{ast.name}"
    
    when "Fn_call"
      jl = []
      for v in ast.arg_list
        jl.push gen v, ctx
      "(#{gen ast.fn, ctx})(#{jl.join ', '})"
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
        if #{cond} {
          #{make_tab t, '  '};
        }
        """
      else if t == ''
        """
        if !(#{cond}) {
          #{make_tab f, '  '};
        }
        """
      else
        """
        if #{cond} {
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
        when #{k}
          #{make_tab gen(v, ctx) or '0', '  '}
        """
      
      if "" != f = gen ast.f, ctx
        jl.push """
        else
          #{make_tab f, '  '}
        """
      
      """
      switch #{gen ast.cond, ctx}
        #{join_list jl, '  '}
      """
    
    when "Loop"
      """
      loop {
        #{make_tab gen(ast.scope, ctx), '  '};
      }
      """
    
    when "While"
      """
      while #{gen ast.cond, ctx} {
        #{make_tab gen(ast.scope, ctx), '  '};
      }
      """
    
    when "Break"
      "break"
    
    when "Continue"
      "continue"
    
    when "For_range"
      aux_step = ""
      if ast.step
        aux_step = " by #{gen ast.step, ctx}"
      ranger = if ast.exclusive then "..." else ".."
      """
      for #{gen ast.i, ctx} in [#{gen ast.a, ctx} #{ranger} #{gen ast.b, ctx}]#{aux_step}
        #{make_tab gen(ast.scope, ctx), '  '}
      """
    
    when "For_col"
      if ast.t.type.main == 'array'
        if ast.v
          aux_v = gen ast.v, ctx
        else
          aux_v = "_skip"
        
        aux_k = ""
        if ast.k
          aux_k = ",#{gen ast.k, ctx}"
        """
        for #{aux_v}#{aux_k} in #{gen ast.t, ctx}
          #{make_tab gen(ast.scope, ctx), '  '}
        """
      else
        if ast.k
          aux_k = gen ast.k, ctx
        else
          aux_k = "_skip"
        
        aux_v = ""
        if ast.v
          aux_v = ",#{gen ast.v, ctx}"
        """
        for #{aux_k}#{aux_v} of #{gen ast.t, ctx}
          #{make_tab gen(ast.scope, ctx), '  '}
        """
    
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
      "let mut #{ast.name}:#{type_recast ast.type}"
    
    when "Class_decl"
      ctx_nest = ctx.mk_nest()
      ctx_nest.in_class = true
      """
      class #{ast.name}
        #{make_tab gen(ast.scope, ctx_nest), '  '}
      """
    
    when "Fn_decl"
      arg_list = ast.arg_name_list
      if ctx.in_class
        """
        #{ast.name} : (#{arg_list.join ', '})->
          #{make_tab gen(ast.scope, ctx), '  '}
        """
      else
        sgnt_list = ast.type.nest_list
        sgnt_string = "("
        for t, i in sgnt_list[1..]
          sgnt_string += ", " if i != 0
          sgnt_string += "#{arg_list[i]}:#{type_recast t}"
        sgnt_string += ")"
        if sgnt_list[0].main != "void"
          sgnt_string += " -> #{type_recast sgnt_list[0]}"
        """
        fn #{ast.name}#{sgnt_string} {
          #{make_tab gen(ast.scope, ctx), '  '}
        }
        """
    