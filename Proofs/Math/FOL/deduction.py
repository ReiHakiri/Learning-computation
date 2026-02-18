from parsing import *

def self_imply(p: tuple, q: tuple) -> tuple:
    return (('i', -1), p, (('i', -1), q, p))

def imply_dist(p: tuple, q: tuple, r: tuple) -> tuple:
    return (('i', -1), (('i', -1), p, (('i', -1), q, r)), (('i', -1), (('i', -1), p, q), (('i', -1), p, r)))

def contradiction(p: tuple, q: tuple) -> tuple:
    return (('i', -1), (('i', -1), (('n', -1), p), (('n', -1), q)), (('i', -1), q, p))

def uni_distr(p: tuple) -> tuple:
    if len(p) == 1:
        raise Exception()
    
    if p[0][0] == 'F' and p[1][0][0] == 'i':
        return (('i', -1), (('F', -1), p[1][1]), (('F', -1), p[1][2]))
    
    else:
        raise Exception()
    
def uni_gen(p: tuple, first = True, depth = 0) -> tuple:
    if first:
        return (('F', -1), uni_gen(p, False))
    
    if len(p) == 1:
        prefix, index = p[0]

        if prefix == 'v':
            if index >= depth:
                return ((prefix, index + 1),)
            
            else:
                return ((prefix, index),)
        
        else:
            return p
        
    if p[0][0] == 'F':
        depth += 1
        
    result = [p[0]]

    p = p[1:]

    for c in p:
        result.append(uni_gen(c, first), first, depth)

    return tuple(result)

from parsing import *

def increment_var(expr: tuple, depth = 0):
    if len(expr) == 1:
        prefix, index = expr[0]

        if prefix == 'v':
            return ((prefix, index + depth + 1),)
        
        else:
            return expr
        
    result = [expr[0]]

    expr = expr[1:]

    for c in expr:
        result.append(increment_var(c, depth))

    return tuple(result)

def is_term(term: tuple) -> bool:
    if len(term) == 1:
        return True

    prefix, _ = term[0]

    result = True

    if prefix in {'f', 'p'}:
        for c in term[1:]:
            result = result and is_term(c)

        return result
    
    else:
        return False

def substitute_1(expr: tuple, term: tuple, depth = 0, first = True) -> tuple:
    if not is_term(term):
        raise Exception()
    
    if first:
        if expr[0][0] in 'F':
            return substitute_1(expr[1], term, first = False)
        
        else:
            return expr
        
    if len(expr) == 1:
        prefix, index = expr[0]

        if prefix == 'v':
            if index == depth:
                return increment_var(term, depth)

            elif index > depth:
                return ((prefix, index - 1))
            
        else:
            return ((prefix, index),)
    
    prefix = expr[0]

    result = [prefix]

    if prefix[0] in {'M', 'F'}:
        depth += 1

    for c in expr[1:]:
        result.append(substitute_1(c, term, depth, first))

    return tuple(result)

'''
expr = '(F(i(F(p0v1v0))(p0v0v0)))'
term = '(f0v1v0)'
n_args = {'p': [2], 'f': [2]}

expr = parse(expr, n_args)
term = parse(term, n_args)

print(i_parse(substitute(expr, term)))
'''
    
def uni_substitution(p: tuple, term: tuple) -> tuple:
    if len(p) == 1:
        raise Exception()
    
    if p[0][0] == 'F':
        return substitute_1(p, term)
    
    else:
        raise Exception()
    
def substitute_2(expr: tuple, term: tuple, depth = 0, first = True) -> tuple:
    if is_term(term):
        raise Exception()
    
    if first:
        if expr[0][0] in 'M':
            return substitute_2(expr[1], term, first = False)
        
        else:
            return expr
        
    if len(expr) == 1:
        prefix, index = expr[0]

        if prefix == 'v':
            if index == depth:
                return term

            elif index > depth:
                return ((prefix, index - 1))
            
        else:
            return ((prefix, index),)
    
    prefix = expr[0]

    result = [prefix]

    if prefix[0] in {'M', 'F'}:
        depth += 1

    for c in expr[1:]:
        result.append(substitute_2(c, term, depth, first))

    return tuple(result)

def meta_substitution(p: tuple, q: tuple):
    if len(p) == 1:
        raise Exception()
    
    if p[0][0] == 'M':
        return substitute_2(p, q)
    
    else:
        raise Exception()

def reflexivity(v1: tuple) -> tuple:
    if len(v1) == 1 and v1[0][0] == 'v':
        return (('=', -1), v1, v1)
    
    else:
        raise Exception()
    
def equality_replace(p: tuple, replace: int, on = 0, depth = 0) -> tuple:
    prefix, index = p[0]

    if len(p) == 1:
        if prefix == 'v' and index == depth + 1:
            on += 1

            if on == replace:
                return (('v', depth),)
            
            else:
                return ((prefix, index),)
            
        else:
            return ((prefix, index),)
    
    result = [p[0]]

    if p[0][0] == 'F':
        depth += 1

    p = p[1:]

    for c in p:
        result.append(equality_replace(c, replace, on, depth))

    return tuple(result)
    
def equality_sub(p: tuple, replace: int) -> tuple:
    sub_p = equality_replace(p, replace)

    return (('F', -1), (('F', -1), (('i', -1), (('=', -1), (('v', 1),), (('v', 0),)), (('i', -1), p, sub_p))))
    
def modus_ponens(deduction: tuple, context: tuple, p: tuple) -> tuple:
    if len(p) < 3:
        raise Exception()
    
    if p[0][0] == 'i':
        if p[1] in deduction or p[1] in context:
            return p[2]
        
        else:
            raise Exception()
    
    else:
        raise Exception()