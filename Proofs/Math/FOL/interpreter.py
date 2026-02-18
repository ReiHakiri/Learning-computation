from parsing import *
from deduction import *
from display import *

def find_n_args(file: list[str]) -> dict:
    file = [line.split('|')[0].strip() for line in file]

    if file[0] == 'Language' or len(file) <= 3:
        n_p = file[1].split(' ')
        n_f = file[2].split(' ')

        new_n_p = []
        new_n_f = []

        for n in n_p:
            new_n_p.append(int(n))

        for n in n_f:
            new_n_f.append(int(n))

        return file[4:], {'p': tuple(new_n_p), 'f': tuple(new_n_f)}
    
    else:
        raise Exception()
    
def find_context(file: list[str], n_args: dict) -> tuple[list[str], set]:
    if file[0] != 'Context' or len(file) == 1:
        raise Exception()
    
    result = []

    read = 1

    for line in file[1:]:
        read += 1

        if line == '':
            break

        _, line = line.split('. ')

        result.append(parse(line, n_args))

    if read == len(file):
        raise Exception('No proof')

    return file[read:], tuple(result)

def separate_proofs(file: list[str]) -> list:
    result = []

    proof = []

    for line in file:
        if line == '':
            result.append(proof)
            proof = []

        else:
            proof.append(line)
    
    result.append(proof)

    return result

def line_tokenize(s: list) -> list:
    result = []

    index = 0

    while index < len(s):
        if s[index] in {'proof', 'context'}:
            if index + 1 < len(s):
                result.append((s[index], s[index + 1]))

                index += 2

            else:
                raise Exception()
            
        else:
            result.append(s[index])

            index += 1

    return result

def proofs_to_deductions(files: list, n_args: dict, context: set) -> tuple:
    deductions = []

    for i, file in enumerate(files):
        deduction = []

        for j, line in enumerate(file):
            if len(line) >= 6 and line[:6] == 'Proof ':
                if line == 'Proof ' + str(i + 1):
                    continue

                else:
                    raise Exception()
                
            if line.split(' ')[0] != str(j) + '.':
                raise Exception('here')
            
            line = line[3:]
            line = line.split()

            line = line_tokenize(line)

            prefix = line.pop(0)

            args = []

            for c in line:
                if isinstance(c, tuple):
                    instance, n = c

                    if instance == 'context':
                        args.append(context[int(n) - 1])

                    elif instance == 'proof':                        
                        n = tuple(n.split('.'))

                        if len(n) != 2:
                            raise Exception()
                        
                        n1, n2 = n
                        n1, n2 = int(n1) - 1, int(n2) - 1

                        if n1 == len(deductions) and n2 < j:
                            args.append(deduction[n2])
                        
                        elif 0 < n1 < len(deductions) and n2 < j:
                            args.append(deductions[n1][n2])

                        else:
                            raise Exception()
                        
                elif c == 'prev':
                        if len(deduction) > 0:
                            args.append(deduction[-1])
                        
                        else:
                            raise Exception()

                else:
                    if c.isnumeric():
                        args.append(int(c))
                    
                    else:
                        args.append(parse(c, n_args))

            if prefix == 'iself':
                if len(args) == 2:
                    deduction.append(self_imply(args[0], args[1]))

                else:
                    raise Exception()
                
            elif prefix == 'idist':
                if len(args) == 3:
                    deduction.append(imply_dist(args[0], args[1], args[2]))

                else:
                    raise Exception()
                
            elif prefix == 'contradict':
                if len(args) == 2:
                    deduction.append(contradiction(args[0], args[1]))

                else:
                    raise Exception()
                
            elif prefix == 'msub':
                if len(args) == 2:
                    deduction.append(meta_substitution(args[0], args[1]))

                else:
                    raise Exception()
                
            elif prefix == 'udist':
                if len(args) == 1:
                    deduction.append(uni_distr(args[0]))

                else:
                    raise Exception()
                
            elif prefix == 'gen':
                if len(args) == 1:
                    deduction.append(uni_gen(args[0]))

                else:
                    raise Exception()
                
            elif prefix == 'usub':
                if len(args) == 2:
                    deduction.append(uni_substitution(args[0], args[1]))
                
                else:
                    raise Exception()
                
            elif prefix == 'reflexive':
                if len(args) == 1:
                    if len(args[0]) == 1 and args[0][0][0] == 'v':
                        deduction.append(reflexivity(args[0]))
                    
                    else:
                        raise Exception()
                    
                else:
                    raise Exception()
            
            elif prefix == 'esub':
                if len(args) == 2:
                    deduction.append(equality_sub(args[0], args[1]))
                    
                else:
                    raise Exception()
                
            elif prefix == 'mp':
                if len(args) == 1:
                    deduction.append(modus_ponens(deduction, context, args[0]))

                else:
                    raise Exception()
            
            else:
                raise Exception()
                
        deductions.append(tuple(deduction))

    return tuple(deductions)

def deductions_to_latex(context: tuple, deductions: list, current_file_name: str, new_file_name: str) -> str:
    context_latex = ', '.join(tree_to_latex(axiom) for axiom in context)

    result = r'''\documentclass[12pt]{article}
    
''' + r'\title{' + current_file_name + '}' + r'''

\begin{document}
\maketitle

$A = \{''' + context_latex  + r'''\}$\\''' + '\n'
    
    for i, deduction in enumerate(deductions):
        result += r'''\\
        
Proof'''

        result += ' ' + str(i + 1) + r'\\' + '\n' + r'\\' + '\n'

        for formula in deduction:
            result += r'$A \vdash ' + tree_to_latex(formula) + r'$\\' + '\n' + r'\\' + '\n'

    result += '\n' + r'\end{document}'

    with open('latex_files/' + new_file_name, 'w') as file:
        file.write(result)

    return result