LOGIC_C = {'M', 'F', 'i', 'n', '='}
BRAC_C = {'(', ')'}
NONNUM_C = LOGIC_C | BRAC_C
NUM_C = {'f', 'p', 'v', 'c'}

def tokenize(s: str) -> tuple:
    result = []

    pair = []
    n = ''

    for i, c in enumerate(s):
        if len(pair) == 1:
            if not c.isnumeric():
                raise Exception()
            
            n += c

            if i + 1 == len(s) or s[i + 1] in NONNUM_C | NUM_C:
                pair.append(int(n))                
                result.append(tuple(pair))

                pair = []
                n = ''

        elif c in NONNUM_C:
            result.append((c, -1))
        
        elif c in NUM_C:
            pair.append(c)

        else:
            raise Exception()

    return tuple(result)

def i_tokenize(s: tuple) -> str:
    result = ''

    for c, n in s:
        result += c

        if n != -1:
            result += str(n)

    return result

#print(i_tokenize(tokenize('(F(i(p0c0v0)(F(p0v0v1))))')))

def arguments(s: tuple) -> tuple:
    result = []

    arg = []
    n_bracs = 0

    for c, i in s:
        arg.append((c, i))

        if c == '(':
            n_bracs += 1

        elif c == ')':
            n_bracs -= 1

        if n_bracs == 0:
            result.append(tuple(arg))

            arg = []

    if n_bracs != 0:
        raise Exception()

    return tuple(result)

#print(arguments(tokenize('(p0v0)(F(p0v0))')))

def tree(s: tuple, n_args: dict[str, list[int]]) -> tuple:
    if len(s) < 3:
        if len(s) == 1 and s[0][0] in {'v', 'c'}:
            return (s)
        
        else:
            raise Exception()
        
    prefix, index = s[1]

    s = s[2:-1]

    terms = arguments(s)

    working = [(prefix, index)]

    if prefix in {'M', 'F', 'n'}:
        if len(terms) == 1:
            working.append(tree(terms[0], n_args))

            return tuple(working)
        
        else:
            raise Exception()
        
    elif prefix in {'i', '='}:
        if len(terms) == 2:
            working.append(tree(terms[0], n_args))
            working.append(tree(terms[1], n_args))

            return tuple(working)
        
        else:
            raise Exception()
        
    elif prefix in {'f', 'p'}:
        n_arg = n_args[prefix][index]

        if len(terms) == n_arg:
            for term in terms:
                working.append(tree(term, n_args))
            
            return tuple(working)
        
        else:
            raise Exception()
    
    else:
        raise Exception()
    
def parse(s: str, n_args: dict[str, list[int]]) -> tuple:
    return tree(tokenize(s), n_args)

def i_parse(s: tuple) -> str:
    prefix, index = s[0]

    if prefix in {'v', 'c'}:
        return prefix + str(index)
    
    if prefix in NUM_C:
        result = '(' + prefix + str(index)

    else:
        result = '(' + prefix

    for c in s[1:]:
        result += i_parse(c)

    return result + ')'

#print(i_parse(parse('(F(i(p0v1c1)(p0v2v2)))', {'p': [2], 'f': []})))

def tree_to_latex(s: tuple) -> str:
    prefix, index = s[0]

    if len(s) == 1:
        return f'{prefix}_{index}'
    
    s = s[1:]

    result  = ''

    if prefix == 'M':
        result += r'( \phi' + tree_to_latex(s[0]) + ')'

    elif prefix == 'F':
        result += r'( \forall ' + tree_to_latex(s[0]) + ')'

    elif prefix == 'i':
        result = '(' + tree_to_latex(s[0]) + r' \rightarrow ' + tree_to_latex(s[1]) + ')'

    elif prefix == 'n':
        result = '(' + r' \neg ' + tree_to_latex(s[0]) + ')'

    elif prefix == '=':
        result = '(' + tree_to_latex(s[0]) + ' = ' + tree_to_latex(s[1]) + ')'

    elif prefix in {'f', 'p'}:
        result += f'{prefix}_{index}' + '('

        for c in s:
            result += tree_to_latex(c) + ','

        result = result[:-1]

        result += ')'

    return result

#print(parse('(F(F(=(f2v1(f0v0))(f1(f2v1v0)v1))))', {'p': [2, 2], 'f': [1, 2, 2, 2]}))
#print(parse('(F(F(p1v1v0)))', {'p': [2, 2], 'f': [1, 2, 2, 2]}))