require "fy"
assert = require 'assert'

mod = require '../src/index.coffee'
gen = mod.gen
Type = require 'type'
type = (t)->new Type t
ast = require 'ast4gen'

var_d = (name, scope, _type='int')->
  scope.list.push t = new ast.Var_decl
  t.name = name
  t.type = type _type
  
  t = new ast.Var
  t.name = name
  t.type = type _type
  t

_var = (name, _type='int')->
  t = new ast.Var
  t.name = name
  t.type = type _type
  t

cst = (_type, val)->
  t = new ast.Const
  t.val = val
  t.type = type _type
  t

ci = (val)->
  t = new ast.Const
  t.val = val
  t.type = type 'int'
  t

cs = (val)->
  t = new ast.Const
  t.val = val
  t.type = type 'string'
  t

un = (a, op)->
  t = new ast.Un_op
  t.a = a
  t.op= op
  t

bin = (a, op, b)->
  t = new ast.Bin_op
  t.a = a
  t.b = b
  t.op= op
  t

fnd = (name, _type, arg_name_list, scope_list)->
  t = new ast.Fn_decl
  t.name = name
  t.arg_name_list = arg_name_list
  t.type = type _type
  t.scope.list = scope_list
  t

fa = (target, name, _type)-> # a.b: a - target, b - name
  t = new ast.Field_access
  t.t = target
  t.name = name
  t.type = type _type
  t

describe 'index section', ->
  it "var x = 5; (js)", ->
    decl = new ast.Var_decl
    decl.name = "x"
    decl.type = new Type "int"

    var_x = new ast.Var
    var_x.name = "x"
    var_x.type = new Type "int"

    const_5 = new ast.Const
    const_5.val = "5"
    const_5.type = new Type "int"

    bin_op = new ast.Bin_op
    bin_op.op = "ASSIGN"
    bin_op.a = var_x
    bin_op.b = const_5
    bin_op.type = new Type "int"

    scope = new ast.Scope
    scope.list.push decl
    scope.list.push bin_op

    scope.validate()
    assert.equal gen(scope), """
      int x;
      x = 5
    """

  it 'this', ->
    assert.equal gen(_var('this', 'int')), "this"
    return
  
  it '1', ->
    scope = new ast.Scope
    scope.list.push cst "int", "1"
    assert.equal gen(scope), "1"
    return
  
  it '1.1', ->
    scope = new ast.Scope
    scope.list.push cst "float", "1.1"
    assert.equal gen(scope), "1.1f"
    return
  
  it '"1"', ->
    scope = new ast.Scope
    scope.list.push cst "string", "1"
    assert.equal gen(scope), '"1"'
    return
  
  it 'true', ->
    scope = new ast.Scope
    scope.list.push cst "bool", "true"
    assert.equal gen(scope), "true"
    return
  
  it 'a', ->
    scope = new ast.Scope
    var_a = new ast.Var
    var_a.name = "a"
    # var_a.type = new Type "int"   # unnecessary for this particular test
    scope.list.push var_a
    assert.equal gen(scope), "a"
    return
  
  it '+"3.14"', ->
    scope = new ast.Scope
    c = cst "string", "3.14"
    scope.list.push un(c, "PLUS")
    assert.equal gen(scope), 'Float.parseFloat("3.14")'
    return
  
  it '-1', ->
    scope = new ast.Scope
    c = cst "int", "1"
    scope.list.push un(c, "MINUS")
    assert.equal gen(scope), "-(1)"
    return
  
  it '!true', ->
    scope = new ast.Scope
    c = cst "bool", "true"
    scope.list.push un(c, "BOOL_NOT")
    assert.equal gen(scope), "!(true)"
    return
  
  it '!5', ->
    scope = new ast.Scope
    c = cst "int", "5"
    scope.list.push un(c, "BIT_NOT")
    assert.equal gen(scope), "~(5)"
    return
  
  it 'a?', ->
    scope = new ast.Scope
    c = cst "int", "1"
    scope.list.push un(c, "IS_NOT_NULL")
    assert.equal gen(scope), "(1 != null)"
    return
  
  it "var a = 5; a++", ->
    scope = new ast.Scope
    a = var_d "a", scope
    c = cst "int", "5"
    scope.list.push bin(a, "ASSIGN", c)
    scope.list.push un(a, "RET_INC")
    assert.equal gen(scope), """
      int a;
      a = 5;
      (a)++
    """
  
  it "var a = 5; a--", ->
    scope = new ast.Scope
    a = var_d "a", scope
    c = cst "int", "5"
    scope.list.push bin(a, "ASSIGN", c)
    scope.list.push un(a, "RET_DEC")
    assert.equal gen(scope), """
      int a;
      a = 5;
      (a)--
    """
  
  it "var a = 5; ++a", ->
    scope = new ast.Scope
    a = var_d "a", scope
    c = cst "int", "5"
    scope.list.push bin(a, "ASSIGN", c)
    scope.list.push un(a, "INC_RET")
    assert.equal gen(scope), """
      int a;
      a = 5;
      ++(a)
    """
  
  it "var a = 5; --a", ->
    scope = new ast.Scope
    a = var_d "a", scope
    c = cst "int", "5"
    scope.list.push bin(a, "ASSIGN", c)
    scope.list.push un(a, "DEC_RET")
    assert.equal gen(scope), """
      int a;
      a = 5;
      --(a)
    """
  
  # TODO refactoring
  it '2 + 2', ->
    scope = new ast.Scope
    l = r = cst "int", "2"
    scope.list.push bin(l, "ADD", r)
    assert.equal gen(scope), "(2 + 2)"
    return
  
  it '2 - 2.2', ->
    scope = new ast.Scope
    a = cst "int", "2"
    b = cst "float", "2.2"
    op = bin(a, "SUB", b)
    op.type = new Type "float"
    scope.list.push op
    assert.equal gen(scope), "(2 - 2.2f)"
    return
  
  it '2.2 * 2', ->
    scope = new ast.Scope
    a = cst "float", "2.2"
    b = cst "int", "2"
    op = bin(a, "MUL", b)
    op.type = new Type "float"
    scope.list.push op
    assert.equal gen(scope), "(2.2f * 2)"
    return
  
  it '5 / 2', ->
    scope = new ast.Scope
    a = cst "int", "5"
    b = cst "int", "2"
    op = bin(a, "DIV", b)
    op.type = new Type "float"
    scope.list.push op
    assert.equal gen(scope), "(5.0f / 2)"
    return
  
  it '5 // 2 int', ->
    scope = new ast.Scope
    a = cst "int", "5"
    b = cst "int", "2"
    op = bin(a, "DIV", b)
    op.type = new Type "float"
    scope.list.push op
    assert.equal gen(scope), "(5 / 2)"
    return
  
  it '5 % 3', ->
    scope = new ast.Scope
    a = cst "int", "5"
    b = cst "int", "3"
    op = bin(a, "MOD", b)
    op.type = new Type "int"
    scope.list.push op
    assert.equal gen(scope), "(5 % 3)"
    return
  
  it '5 ** 2', ->
    scope = new ast.Scope
    a = cst "int", "5"
    b = cst "int", "2"
    op = bin(a, "POW", b)
    op.type = new Type "int"
    scope.list.push op
    assert.equal gen(scope), "Math.pow(5, 2)"
    return
  
  it '5.5 ** 2', ->
    scope = new ast.Scope
    a = cst "float", "5.5"
    b = cst "int", "2"
    op = bin(a, "POW", b)
    op.type = new Type "float"
    scope.list.push op
    assert.equal gen(scope), "Math.pow(5.5f, 2)"
    return
  
  it '5 ** 2.5', ->
    scope = new ast.Scope
    a = cst "int", "5"
    b = cst "float", "2.5"
    op = bin(a, "POW", b)
    op.type = new Type "float"
    scope.list.push op
    assert.equal gen(scope), "Math.pow(5, 2.5f)"
    return
  
  it '5.5 ** 2.5', ->
    scope = new ast.Scope
    a = cst "float", "5.5"
    b = cst "float", "2.5"
    op = bin(a, "POW", b)
    op.type = new Type "float"
    scope.list.push op
    assert.equal gen(scope), "Math.pow(5.5f, 2.5f)"
    return
    
  # it '2 ** true throws', ->
  #   scope = new ast.Scope
  #   a = cst "int", "2"
  #   b = cst "bool", "true"
  #   op = bin(a, "POW", b)
  #   op.type = new Type "float"
  #   scope.list.push op
  #   assert.throws(-> gen scope)
  #   return
  
  # it '2.5 ** true throws', ->
  #   scope = new ast.Scope
  #   a = cst "float", "2.5"
  #   b = cst "bool", "true"
  #   op = bin(a, "POW", b)
  #   op.type = new Type "float"
  #   scope.list.push op
  #   assert.throws(-> gen scope)
  #   return
  
  # it 'false ** true throws', ->
  #   scope = new ast.Scope
  #   a = cst "bool", "false"
  #   b = cst "bool", "true"
  #   op = bin(a, "POW", b)
  #   op.type = new Type "float"
  #   scope.list.push op
  #   assert.throws(-> gen scope)
  #   return
  
  it 'true && false', ->
    scope = new ast.Scope
    l = cst "bool", "true"
    r = cst "bool", "false"
    scope.list.push bin(l, "BOOL_AND", r)
    assert.equal gen(scope), "(true && false)"
    return
  
  it 'true || false', ->
    scope = new ast.Scope
    l = cst "bool", "true"
    r = cst "bool", "false"
    scope.list.push bin(l, "BOOL_OR", r)
    assert.equal gen(scope), "(true || false)"
    return
  
  it 'true ^^ false', ->
    scope = new ast.Scope
    l = cst "bool", "true"
    r = cst "bool", "false"
    scope.list.push bin(l, "BOOL_XOR", r)
    assert.equal gen(scope), "(true ^ false)"
    return
  
  it '5 & 7', ->
    scope = new ast.Scope
    l = cst "int", "5"
    r = cst "int", "7"
    scope.list.push bin(l, "BIT_AND", r)
    assert.equal gen(scope), "(5 & 7)"
    return
  
  it '5 | 7', ->
    scope = new ast.Scope
    l = cst "int", "5"
    r = cst "int", "7"
    scope.list.push bin(l, "BIT_OR", r)
    assert.equal gen(scope), "(5 | 7)"
    return
  
  it '5 ^ 7', ->
    scope = new ast.Scope
    l = cst "int", "5"
    r = cst "int", "7"
    scope.list.push bin(l, "BIT_XOR", r)
    assert.equal gen(scope), "(5 ^ 7)"
    return
  
  it '17 >> 3', ->
    scope = new ast.Scope
    l = cst "int", "17"
    r = cst "int", "3"
    scope.list.push bin(l, "SHR", r)
    assert.equal gen(scope), "(17 >> 3)"
    return
  
  it '17 << 3', ->
    scope = new ast.Scope
    l = cst "int", "17"
    r = cst "int", "3"
    scope.list.push bin(l, "SHL", r)
    assert.equal gen(scope), "(17 << 3)"
    return
  
  it '17 >>> 3', ->
    scope = new ast.Scope
    l = cst "int", "17"
    r = cst "int", "3"
    scope.list.push bin(l, "LSR", r)
    assert.equal gen(scope), "(17 >>> 3)"
    return
  
  it "var a = 5; a += 1", ->
    scope = new ast.Scope
    a = var_d "a", scope
    b = cst "int", "5"
    c = cst "int", "1"
    scope.list.push bin(a, "ASSIGN", b)
    scope.list.push bin(a, "ASS_ADD", c)
    assert.equal gen(scope), """
      int a;
      a = 5;
      a += 1
    """
  
  it "var a = 5; a -= 2.5", ->
    scope = new ast.Scope
    a = var_d "a", scope, "float"
    b = cst "int", "5"
    c = cst "float", "2.5"
    
    op = bin(a, "ASSIGN", b)
    op.type = new Type "float"
    scope.list.push op
    
    op = bin(a, "ASS_SUB", c)
    op.type = new Type "float"
    scope.list.push op
    
    assert.equal gen(scope), """
      float a;
      a = 5;
      a -= 2.5f
    """
  
  it "var a = 5.5; a *= 2", ->
    scope = new ast.Scope
    a = var_d "a", scope, "float"
    b = cst "float", "5.5"
    c = cst "int", "2"
    
    op = bin(a, "ASSIGN", b)
    op.type = new Type "float"
    scope.list.push op
    
    op = bin(a, "ASS_MUL", c)
    op.type = new Type "float"
    scope.list.push op
    
    assert.equal gen(scope), """
      float a;
      a = 5.5f;
      a *= 2
    """
  
  it "var a = 5; a /= 2", ->
    scope = new ast.Scope
    a = var_d "a", scope, "float"
    b = cst "int", "5"
    c = cst "int", "2"
    
    op = bin(a, "ASSIGN", b)
    op.type = new Type "float"
    scope.list.push op
    
    op = bin(a, "ASS_DIV", c)
    op.type = new Type "float"
    scope.list.push op
    
    assert.equal gen(scope), """
      float a;
      a = 5;
      a /= 2
    """
  
  it "var a = 5; a %= 3", ->
    scope = new ast.Scope
    a = var_d "a", scope, "int"
    b = cst "int", "5"
    c = cst "int", "3"
    
    op = bin(a, "ASSIGN", b)
    op.type = new Type "int"
    scope.list.push op
    
    op = bin(a, "ASS_MOD", c)
    op.type = new Type "int"
    scope.list.push op
    
    assert.equal gen(scope), """
      int a;
      a = 5;
      a %= 3
    """
  
  it "var a = 5; a **= 2", ->
    scope = new ast.Scope
    a = var_d "a", scope, "int"
    b = cst "int", "5"
    c = cst "int", "2"
    
    op = bin(a, "ASSIGN", b)
    op.type = new Type "int"
    scope.list.push op
    
    op = bin(a, "ASS_POW", c)
    op.type = new Type "int"
    scope.list.push op
    
    assert.equal gen(scope), """
      int a;
      a = 5;
      a = Math.pow(a, 2)
    """
  
  it "var a = 5.5; a **= 2", ->
    scope = new ast.Scope
    a = var_d "a", scope, "float"
    b = cst "float", "5.5"
    c = cst "int", "2"
    
    op = bin(a, "ASSIGN", b)
    op.type = new Type "float"
    scope.list.push op
    
    op = bin(a, "ASS_POW", c)
    op.type = new Type "float"
    scope.list.push op
    
    assert.equal gen(scope), """
      float a;
      a = 5.5f;
      a = Math.pow(a, 2)
    """
  
  it "var a = 5; a **= 2.5", ->
    scope = new ast.Scope
    a = var_d "a", scope, "float"
    b = cst "int", "5"
    c = cst "float", "2.5"
    
    op = bin(a, "ASSIGN", b)
    op.type = new Type "float"
    scope.list.push op
    
    op = bin(a, "ASS_POW", c)
    op.type = new Type "float"
    scope.list.push op
    
    assert.equal gen(scope), """
      float a;
      a = 5;
      a = Math.pow(a, 2.5f)
    """
  
  it "var a = 5.5; a **= 2.5", ->
    scope = new ast.Scope
    a = var_d "a", scope, "float"
    b = cst "float", "5.5"
    c = cst "float", "2.5"
    
    op = bin(a, "ASSIGN", b)
    op.type = new Type "float"
    scope.list.push op
    
    op = bin(a, "ASS_POW", c)
    op.type = new Type "float"
    scope.list.push op
    
    assert.equal gen(scope), """
      float a;
      a = 5.5f;
      a = Math.pow(a, 2.5f)
    """
  
  it "var a = 5; a &= 3", ->
    scope = new ast.Scope
    a = var_d "a", scope, "int"
    b = cst "int", "5"
    c = cst "int", "3"
    
    op = bin(a, "ASSIGN", b)
    op.type = new Type "int"
    scope.list.push op
    
    op = bin(a, "ASS_BIT_AND", c)
    op.type = new Type "int"
    scope.list.push op
    
    assert.equal gen(scope), """
      int a;
      a = 5;
      a &= 3
    """
  
  it "var a = 5; a |= 3", ->
    scope = new ast.Scope
    a = var_d "a", scope, "int"
    b = cst "int", "5"
    c = cst "int", "3"
    
    op = bin(a, "ASSIGN", b)
    op.type = new Type "int"
    scope.list.push op
    
    op = bin(a, "ASS_BIT_OR", c)
    op.type = new Type "int"
    scope.list.push op
    
    assert.equal gen(scope), """
      int a;
      a = 5;
      a |= 3
    """
  
  it "var a = 5; a ^= 3", ->
    scope = new ast.Scope
    a = var_d "a", scope, "int"
    b = cst "int", "5"
    c = cst "int", "3"
    
    op = bin(a, "ASSIGN", b)
    op.type = new Type "int"
    scope.list.push op
    
    op = bin(a, "ASS_BIT_XOR", c)
    op.type = new Type "int"
    scope.list.push op
    
    assert.equal gen(scope), """
      int a;
      a = 5;
      a ^= 3
    """
  
  it "var a = true; a &= false", ->
    scope = new ast.Scope
    a = var_d "a", scope, "bool"
    b = cst "bool", "true"
    c = cst "bool", "false"
    
    op = bin(a, "ASSIGN", b)
    op.type = new Type "bool"
    scope.list.push op
    
    op = bin(a, "ASS_BOOL_AND", c)
    op.type = new Type "bool"
    scope.list.push op
    
    assert.equal gen(scope), """
      boolean a;
      a = true;
      a &= false
    """
  
  it "var a = true; a |= false", ->
    scope = new ast.Scope
    a = var_d "a", scope, "bool"
    b = cst "bool", "true"
    c = cst "bool", "false"
    
    op = bin(a, "ASSIGN", b)
    op.type = new Type "bool"
    scope.list.push op
    
    op = bin(a, "ASS_BOOL_OR", c)
    op.type = new Type "bool"
    scope.list.push op
    
    assert.equal gen(scope), """
      boolean a;
      a = true;
      a |= false
    """
  
  it "var a = true; a ^= false", ->
    scope = new ast.Scope
    a = var_d "a", scope, "bool"
    b = cst "bool", "true"
    c = cst "bool", "false"
    
    op = bin(a, "ASSIGN", b)
    op.type = new Type "bool"
    scope.list.push op
    
    op = bin(a, "ASS_BOOL_XOR", c)
    op.type = new Type "bool"
    scope.list.push op
    
    assert.equal gen(scope), """
      boolean a;
      a = true;
      a ^= false
    """
  
  it "var a = 17; a >>= 3", ->
    scope = new ast.Scope
    a = var_d "a", scope, "int"
    b = cst "int", "17"
    c = cst "int", "3"
    
    op = bin(a, "ASSIGN", b)
    op.type = new Type "int"
    scope.list.push op
    
    op = bin(a, "ASS_SHR", c)
    op.type = new Type "int"
    scope.list.push op
    
    assert.equal gen(scope), """
      int a;
      a = 17;
      a >>= 3
    """
  
  it "var a = 17; a <<= 3", ->
    scope = new ast.Scope
    a = var_d "a", scope, "int"
    b = cst "int", "17"
    c = cst "int", "3"
    
    op = bin(a, "ASSIGN", b)
    op.type = new Type "int"
    scope.list.push op
    
    op = bin(a, "ASS_SHL", c)
    op.type = new Type "int"
    scope.list.push op
    
    assert.equal gen(scope), """
      int a;
      a = 17;
      a <<= 3
    """
  
  it "var a = 17; a >>>= 3", ->
    scope = new ast.Scope
    a = var_d "a", scope, "int"
    b = cst "int", "17"
    c = cst "int", "3"
    
    op = bin(a, "ASSIGN", b)
    op.type = new Type "int"
    scope.list.push op
    
    op = bin(a, "ASS_LSR", c)
    op.type = new Type "int"
    scope.list.push op
    
    assert.equal gen(scope), """
      int a;
      a = 17;
      a >>>= 3
    """
  
  it '5 >= 5', ->
    scope = new ast.Scope
    l = r = cst "int", "5"
    scope.list.push bin(l, "GTE", r)
    assert.equal gen(scope), "(5 >= 5)"
    return
  
  it '5.5 <= 5.5', ->
    scope = new ast.Scope
    l = r = cst "float", "5.5"
    scope.list.push bin(l, "LTE", r)
    assert.equal gen(scope), "(5.5f <= 5.5f)"
    return
  
  it 'true == true', ->
    scope = new ast.Scope
    l = r = cst "bool", "true"
    scope.list.push bin(l, "EQ", r)
    assert.equal gen(scope), "(true == true)"
    return
  
  it 'true != true', ->
    scope = new ast.Scope
    l = r = cst "bool", "true"
    scope.list.push bin(l, "NE", r)
    assert.equal gen(scope), "(true != true)"
    return
  
  it '"abc" > "abc"', ->
    scope = new ast.Scope
    l = r = cst "string", "abc"
    scope.list.push bin(l, "GT", r)
    assert.equal gen(scope), '("abc" > "abc")'
    return
  
  it '"abc" < "abc"', ->
    scope = new ast.Scope
    l = r = cst "string", "abc"
    scope.list.push bin(l, "LT", r)
    assert.equal gen(scope), '("abc" < "abc")'
    return
  
  # EQ NE GT LT GTE LTE support for int/float combinations is under a question for now
  
  # it '5 != 5.5', ->
  #   scope = new ast.Scope
  #   a = cst "int", "5"
  #   b = cst "float", "5.5"
  #   op = bin(a, "NE", b)
  #   op.type = new Type "float"
  #   scope.list.push op
  #   assert.equal gen(scope), "(5 as float != 5.5)"
  #   return
  
  # it '5.5 <= 5', ->
  #   scope = new ast.Scope
  #   a = cst "float", "5.5"
  #   b = cst "int", "5"
  #   op = bin(a, "LTE", b)
  #   op.type = new Type "float"
  #   scope.list.push op
  #   assert.equal gen(scope), "(5.5 <= 5 as float)"
  #   return
  
  # it '5.5 >= 5.5', ->
  #   scope = new ast.Scope
  #   a = cst "float", "5.5"
  #   b = cst "float", "5.5"
  #   op = bin(a, "GTE", b)
  #   op.type = new Type "float"
  #   scope.list.push op
  #   assert.equal gen(scope), "(5.5 >= 5.5)"
  #   return
  
  # it '5 < 5.5', ->
  #   scope = new ast.Scope
  #   a = cst "int", "5"
  #   b = cst "float", "5.5"
  #   op = bin(a, "LT", b)
  #   op.type = new Type "float"
  #   scope.list.push op
  #   assert.equal gen(scope), "((5 as float) < 5.5)" # Parentheses matter! Won't compile without them
  #   return
  
  # it '5.5 > 5', ->
  #   scope = new ast.Scope
  #   a = cst "float", "5.5"
  #   b = cst "int", "5"
  #   op = bin(a, "GT", b)
  #   op.type = new Type "float"
  #   scope.list.push op
  #   assert.equal gen(scope), "(5.5 > 5 as float)"
  #   return
  
  # it '[]', ->
  #   scope = new ast.Scope
  #   scope.list.push t = new ast.Array_init
  #   assert.equal gen(scope), "[]"   # INVALID RUST CODE; type annotation needed
  #   return
  
  it '[1]'#, ->
    # scope = new ast.Scope
    # c = cst "int", "1"
    # scope.list.push t = new ast.Array_init
    # t.list.push c
    # assert.equal gen(scope), "vec![1]"
    # return
  
  it 'var a:array<int>; a.sort_by_i((a)->-a)', ->
    scope = new ast.Scope
    var_d "a", scope, "array<int>"
    b = fa _var("a", "array<int>"), "sort_by_i", "function<void,function<float,int>>"
    arg = fnd("", "function<float,int>", ["a"], [])
    scope.list.push t = new ast.Fn_call
    t.fn = b
    t.arg_list.push arg
    # pp scope
    assert.equal gen(scope), """
      ArrayList<Integer> a;
      Function<Integer, Float> _sort_by0 = (a)-> {
        
      };
      Collections.sort(a, (_a, _b) ->_sort_by0.apply(_a) - _sort_by0.apply(_b))
    """
    return
  
  it 'var a:array<int>; a.sort_by_f((a)->-a)', ->
    scope = new ast.Scope
    var_d "a", scope, "array<int>"
    b = fa _var("a", "array<int>"), "sort_by_f", "function<void,function<float,int>>"
    arg = fnd("", "function<float,int>", ["a"], [])
    scope.list.push t = new ast.Fn_call
    t.fn = b
    t.arg_list.push arg
    # pp scope
    assert.equal gen(scope), """
      ArrayList<Integer> a;
      Function<Integer, Float> _sort_by0 = (a)-> {
        
      };
      Collections.sort(a, (_a, _b) ->(int)Math.signum(_sort_by0.apply(_a) - _sort_by0.apply(_b)))
    """
    return
  
  # it '{}', ()->
  #   scope = new ast.Scope
  #   scope.list.push t = new ast.Hash_init
  #   assert.equal gen(scope), "{}"
  #   return
  
  # it '{k:a}', ()->
  #   scope = new ast.Scope
  #   a = var_d('a', scope)
  #   scope.list.push t = new ast.Hash_init
  #   t.hash.k = a
  #   assert.equal gen(scope), '{"k": a}'
  #   return
  
  # it '{}', ()->
  #   scope = new ast.Scope
  #   scope.list.push t = new ast.Struct_init
  #   assert.equal gen(scope), "{}"
  #   return
  
  # it '{k:a}', ()->
  #   scope = new ast.Scope
  #   a = var_d('a', scope)
  #   scope.list.push t = new ast.Struct_init
  #   t.hash.k = a
  #   assert.equal gen(scope), '{"k": a}'
  #   return
  
  # it '{k:a}', ()->
  #   scope = new ast.Scope
  #   a = var_d('a', scope)
  #   t = new ast.Struct_init
  #   t.hash.k = a
    
  #   scope.list.push fa(t, 'k', 'int')
  #   assert.equal gen(scope), '{"k": a}.k'
  #   return
  
  it 'f()', ->
    scope = new ast.Scope
    f = new ast.Var
    f.name = "f"
    scope.list.push t = new ast.Fn_call
    t.fn = f
    assert.equal gen(scope), 'f()'
    return
  
  it 'f(5)', ->
    scope = new ast.Scope
    f = new ast.Var
    f.name = "f"
    c = cst "int", "5"
    scope.list.push t = new ast.Fn_call
    t.fn = f
    t.arg_list.push c
    assert.equal gen(scope), 'f(5)'
    return
  
  it 'round(2.71)', ->
    scope = new ast.Scope
    f = new ast.Var
    f.name = "round"
    f.type = new Type "function<int,float>"
    c = cst "float", "2.71"
    scope.list.push t = new ast.Fn_call
    t.fn = f
    t.arg_list.push c
    assert.equal gen(scope), 'Math.round(2.71f)'
    return
  
  it 'abs(-27)', ->
    scope = new ast.Scope
    f = new ast.Var
    f.name = "abs"
    f.type = new Type "function<int,int>"
    c = cst "int", "-27"
    scope.list.push t = new ast.Fn_call
    t.fn = f
    t.arg_list.push c
    assert.equal gen(scope), 'Math.abs(-27)'
    return
  
  # ###################################################################################################
  #    stmt
  # ###################################################################################################
  
  it 'if (true) {5;}', ->
    scope = new ast.Scope
    cond = cst "bool", "true"
    c = cst "int", "5"
    scope.list.push t = new ast.If
    t.cond = cond
    t.t.list.push c
    assert.equal gen(scope), '''
      if (true) {
        5;
      }
    '''
    return
  
  it 'if (true) {5;} else {2;}', ->
    scope = new ast.Scope
    cond = cst "bool", "true"
    c1 = cst "int", "5"
    c2 = cst "int", "2"
    scope.list.push t = new ast.If
    t.cond = cond
    t.t.list.push c1
    t.f.list.push c2
    assert.equal gen(scope), '''
      if (true) {
        5;
      } else {
        2;
      }
    '''
    return
  
  it 'if (true) {} else {2;}', ->
    scope = new ast.Scope
    cond = cst "bool", "true"
    c2 = cst "int", "2"
    scope.list.push t = new ast.If
    t.cond = cond
    t.f.list.push c2
    assert.equal gen(scope), '''
      if (!(true)) {
        2;
      }
    '''
    return
  
  # ###################################################################################################
  # it 'switch a {k:b}', ()->
  #   scope = new ast.Scope
  #   a = var_d('a', scope, 'string')
  #   b = var_d('b', scope)
  #   scope.list.push t = new ast.Switch
  #   t.cond = a
  #   t.hash["k"] = b
  #   assert.equal gen(scope), '''
  #     switch a
  #       when "k"
  #         b
  #   '''
  #   return
  # it 'switch a {k:b}{k2:0}', ()->
  #   scope = new ast.Scope
  #   a = var_d('a', scope, 'string')
  #   b = var_d('b', scope)
  #   scope.list.push t = new ast.Switch
  #   t.cond = a
  #   t.hash["k"] = b
  #   t.hash["k2"] = new ast.Scope
  #   assert.equal gen(scope), '''
  #     switch a
  #       when "k"
  #         b
  #       when "k2"
  #         0
  #   '''
  #   return
  
  # it 'switch a {1:b}', ()->
  #   scope = new ast.Scope
  #   a = var_d('a', scope)
  #   b = var_d('b', scope)
  #   scope.list.push t = new ast.Switch
  #   t.cond = a
  #   t.hash["1"] = b
  #   assert.equal gen(scope), '''
  #     switch a
  #       when 1
  #         b
  #   '''
  #   return
  
  it 'switch 0 {1:2} default{3}', ->
    scope = new ast.Scope
    a = cst "int", "0"
    b = cst "int", "2"
    c = cst "int", "3"
    scope.list.push t = new ast.Switch
    t.cond = a
    t.hash["1"] = b
    t.f.list.push c
    assert.equal gen(scope), '''
      switch (0) {
        case 1:
          2;
          break;
        default:
          3;
          break;
      }
    '''
    return
  # ###################################################################################################
  it 'loop', ->
    scope = new ast.Scope
    a = cst "int", "1"
    scope.list.push t = new ast.Loop
    t.scope.list.push a
    assert.equal gen(scope), '''
      while (true) {
        1;
      }
    '''
    return
  # ###################################################################################################
  it 'while', ->
    scope = new ast.Scope
    a = cst "bool", "true"
    b = cst "int", "1"
    scope.list.push t = new ast.While
    t.cond = a
    t.scope.list.push b
    assert.equal gen(scope), '''
      while (true) {
        1;
      }
    '''
    return
  
  it 'continue', ()->
    assert.equal gen(new ast.Continue), 'continue'
    return
  
  it 'break', ()->
    assert.equal gen(new ast.Break), 'break'
    return
  # ###################################################################################################
  it 'for i in [1 ... 10] 1', ()->
    scope = new ast.Scope
    i = var_d('i', scope)
    a = cst "int", "1"
    
    scope.list.push t = new ast.For_range
    t.i = i
    t.a = ci '1'
    t.b = ci '10'
    t.scope.list.push a
    assert.equal gen(scope), '''
      int i;
      for (i = 1; i < 10; i++) {
        1;
      }
    '''
    return
  
  it 'for i in [1 .. 10] 1', ()->
    scope = new ast.Scope
    i = var_d('i', scope)
    a = cst "int", "1"
    
    scope.list.push t = new ast.For_range
    t.i = i
    t.exclusive = false
    t.a = ci '1'
    t.b = ci '10'
    t.scope.list.push a
    assert.equal gen(scope), '''
      int i;
      for (i = 1; i <= 10; i++) {
        1;
      }
    '''
    return
  
  it 'for i in [1 .. 10] by 2 1', ()->
    scope = new ast.Scope
    i = var_d('i', scope)
    a = cst "int", "1"
    
    scope.list.push t = new ast.For_range
    t.i = i
    t.exclusive = false
    t.a = ci '1'
    t.b = ci '10'
    t.step = ci '2'
    t.scope.list.push a
    assert.equal gen(scope), '''
      int i;
      for (i = 1; i <= 10; i += 2) {
        1;
      }
    '''
    return
  # # ###################################################################################################
  # it 'for v in a b', ()->
  #   scope = new ast.Scope
  #   v = var_d('v', scope)
  #   a = var_d('a', scope)
  #   b = var_d('b', scope)
    
  #   scope.list.push t = new ast.For_col
  #   t.v = v
  #   t.t = a
  #   t.t.type = new Type 'array<int>'
  #   t.scope.list.push b
  #   assert.equal gen(scope), '''
  #     for v in a
  #       b
  #   '''
  #   return
  
  # it 'for v,k in a b', ()->
  #   scope = new ast.Scope
  #   v = var_d('v', scope)
  #   k = var_d('k', scope)
  #   a = var_d('a', scope)
  #   b = var_d('b', scope)
    
  #   scope.list.push t = new ast.For_col
  #   t.k = k
  #   t.v = v
  #   t.t = a
  #   t.t.type = new Type 'array<int>'
  #   t.scope.list.push b
  #   assert.equal gen(scope), '''
  #     for v,k in a
  #       b
  #   '''
  #   return
  
  # it 'for _skip,k in a b', ()->
  #   scope = new ast.Scope
  #   k = var_d('k', scope)
  #   a = var_d('a', scope)
  #   b = var_d('b', scope)
    
  #   scope.list.push t = new ast.For_col
  #   t.k = k
  #   t.t = a
  #   t.t.type = new Type 'array<int>'
  #   t.scope.list.push b
  #   assert.equal gen(scope), '''
  #     for _skip,k in a
  #       b
  #   '''
  #   return
  # # ###################################################################################################
  # it 'for v of a b', ()->
  #   scope = new ast.Scope
  #   v = var_d('v', scope)
  #   a = var_d('a', scope)
  #   b = var_d('b', scope)
    
  #   scope.list.push t = new ast.For_col
  #   t.v = v
  #   t.t = a
  #   t.t.type = new Type 'hash<int>'
  #   t.scope.list.push b
  #   assert.equal gen(scope), '''
  #     for _skip,v of a
  #       b
  #   '''
  #   return
  
  # it 'for v,k of a b', ()->
  #   scope = new ast.Scope
  #   v = var_d('v', scope)
  #   k = var_d('k', scope)
  #   a = var_d('a', scope)
  #   b = var_d('b', scope)
    
  #   scope.list.push t = new ast.For_col
  #   t.k = k
  #   t.v = v
  #   t.t = a
  #   t.t.type = new Type 'hash<int>'
  #   t.scope.list.push b
  #   assert.equal gen(scope), '''
  #     for k,v of a
  #       b
  #   '''
  #   return
  
  # it 'for _skip,k of a b', ()->
  #   scope = new ast.Scope
  #   k = var_d('k', scope)
  #   a = var_d('a', scope)
  #   b = var_d('b', scope)
    
  #   scope.list.push t = new ast.For_col
  #   t.k = k
  #   t.t = a
  #   t.t.type = new Type 'hash<int>'
  #   t.scope.list.push b
  #   assert.equal gen(scope), '''
  #     for k of a
  #       b
  #   '''
  #   return
  # ###################################################################################################
  it 'return', ()->
    scope = new ast.Scope
    scope.list.push t = new ast.Ret
    assert.equal gen(scope), 'return'
    return
  
  it 'return 1', ()->
    scope = new ast.Scope
    scope.list.push t = new ast.Ret
    t.t = ci '1'
    assert.equal gen(scope), 'return (1)'
    return
  # ###################################################################################################
  # it 'try', ()->
  #   scope = new ast.Scope
  #   a = var_d('a', scope)
  #   b = var_d('b', scope)
  #   scope.list.push t = new ast.Try
  #   t.t.list.push a
  #   t.c.list.push b
  #   t.exception_var_name = 'e'
  #   assert.equal gen(scope), '''
  #     try
  #       a
  #     catch e
  #       b
  #   '''
  #   return
  # ###################################################################################################
  it 'panic!("AAAaaaaa!!!!")', ->
    scope = new ast.Scope
    scope.list.push t = new ast.Throw
    t.t = cs "AAAaaaaa!!!!"
    assert.equal gen(scope), 'panic!("AAAaaaaa!!!!")'
    return
  
  it 'Fn_decl empty', ->
    scope = new ast.Scope
    scope.list.push fnd('f', type('function<void>'), [], [])
    assert.equal gen(scope), "public void f() {\n  \n}"
  
  it 'Fn_decl 1 param', ->
    scope = new ast.Scope
    scope.list.push fnd('f', type('function<void,int>'), ["a"], [])
    assert.equal gen(scope), "public void f(int a) {\n  \n}"
  
  it 'Fn_decl 2 params', ->
    scope = new ast.Scope
    scope.list.push fnd('f', type('function<void,float,bool>'), "ab", [])
    assert.equal gen(scope), "public void f(float a, boolean b) {\n  \n}"
    
  it 'Fn_decl return', ->
    scope = new ast.Scope
    ret = new ast.Ret
    ret.t = ci "1"
    scope.list.push fnd('f', type('function<int>'), [], [ret])
    assert.equal gen(scope), '''
      public int f() {
        return (1);
      }
    '''
  
  it 'Fn_decl 2 params return', ->
    scope = new ast.Scope
    ret = new ast.Ret
    ret.t = ci "1"
    scope.list.push fnd('f', type('function<int,float,bool>'), "ab", [ret])
    assert.equal gen(scope), '''
      public int f(float a, boolean b) {
        return (1);
      }
    '''
  
  describe 'Class_decl', ()->
    it 'Empty', ()->
      scope = new ast.Scope
      scope.list.push t = new ast.Class_decl
      t.name = 'A'
      assert.equal gen(scope), '''
        class A {
          
        }
        '''
    
  #   it 'Method', ()->
  #     scope = new ast.Scope
  #     scope.list.push t = new ast.Class_decl
  #     t.name = 'A'
  #     t.scope.list.push fnd('fn', type('function<void>'), [], [])
  #     assert.equal gen(scope), '''
  #       class A
  #         fn : ()->
            
  #       '''