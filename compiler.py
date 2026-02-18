import actions
import parsing
import turing
from collections import deque

DEFAULT = (0, 0, 1)

def written_d(d: str) -> int:
    if d == 'left':
        return -1
    
    elif d == 'right':
        return 1
    
    else:
        raise Exception('Invalid direction')

def convert(file) -> list[list[tuple[int, int, int]]]:
    total_symbols, v_bounds, program = parsing.tokenizer(file)

    total_lines = len(program)

    transition_table = actions.blank_table(total_symbols, total_lines, v_bounds)

    for line_n, line in enumerate(program):
        indents, line = line

        if line[0] == 'halt':
            transition_table = actions.add_halt(transition_table, line_n, total_symbols, total_lines, v_bounds)

        elif line[0] == 'repeat':
            transition_table = actions.add_repeat(transition_table, line_n, total_symbols, total_lines, v_bounds)
        
        elif line[0][0] == 'v':
            i = int(line[0][1:])
            value = int(line[2])

            transition_table = actions.add_assignment(transition_table, line_n, total_symbols, total_lines, v_bounds, i, value)

        elif line[0] == 'if':
            pointer = line_n

            p = None
            p_found = False

            q = None
            q_found = False

            while pointer != total_lines:
                search_indents, search_line = program[pointer]

                if search_line[0] == 'else' and search_indents == indents and not p_found:
                    p = pointer + 1
                    p_found = True

                elif p_found and search_indents == indents:
                    q = pointer
                    q_found = True

                if p_found and q_found:
                    break

                pointer += 1

            if p == None:
                raise Exception('Missing else for if')
            
            if q == None:
                q = total_lines + 1

            if line[1][0] == 'v':
                i = int(line[1][1:])
                value = int(line[3])

                transition_table = actions.add_if_variable(transition_table, line_n, total_symbols, total_lines, v_bounds, i, value, p, q)

            elif line[1] == 'S':
                m = int(line[3])

                transition_table = actions.add_if_symbol(transition_table, line_n, total_symbols, total_lines, v_bounds, m, p, q)

            else:
                raise Exception('Invalid comparison target')
            
        elif line[0] == 'change':
            m = int(line[1])
            d = written_d(line[2])

            transition_table = actions.add_change(transition_table, line_n, total_symbols, total_lines, v_bounds, m, d)

        elif line[0] == 'overwrite':
            m = int(line[1])

            transition_table = actions.add_overwrite(transition_table, line_n, total_symbols, total_lines, v_bounds, m)

        elif line[0] == 'move':
            d = written_d(line[1])

            transition_table = actions.add_move(transition_table, line_n, total_symbols, total_lines, v_bounds, d)

        elif line[0] == 'until':
            pointer = line_n

            p = None

            while pointer != total_lines:
                search_indents, search_line = program[pointer]

                if search_line[0] == 'id' and search_indents == indents:
                    p = pointer
                    break

                pointer += 1

            if p == None:
                raise Exception('Missing id for until')

            if line[1][0] == 'v':
                i = int(line[1][1:])
                value = int(line[3])

                transition_table = actions.add_until_variable(transition_table, line_n, total_symbols, total_lines, v_bounds, i, value, p)

            elif line[1] == 'S':
                m = int(line[3])

                transition_table = actions.add_until_symbol(transition_table, line_n, total_symbols, total_lines, v_bounds, m, p)

            else:
                raise Exception('Invalid comparison target')
        
        elif line[0] == 'else':
            if line_n + 1 == total_symbols:
                transition_table = actions.add_halt(transition_table, line_n, total_symbols, total_lines, v_bounds)
            
            continue

        elif line[0] == 'id':
            if line_n + 1 == total_symbols:
                transition_table = actions.add_halt(transition_table, line_n, total_symbols, total_lines, v_bounds)
            
            continue

        else:
            raise Exception('Invalid operation', line)
        
    return total_lines, v_bounds, transition_table

# print(convert(open('test_and.txt')))

def clean(transition_table: list[list[tuple[int, int, int]]], default: tuple[int, int, int]) -> tuple[tuple[tuple[int, int, int]]]:
    result = []

    for row in transition_table:
        new_row = []

        for element in row:
            if element == None:
                new_row.append(default)
            
            else:
                new_row.append(element)
        
        result.append(tuple(new_row))

    return tuple(result)

# print(clean(convert(open('test_and.txt')), DEFAULT))

def get_TM(tape: tuple[int], transition_table: tuple[tuple[tuple[int, int, int]]], total_lines: int, v_bounds: list[int]) -> turing.TuringMachine:
    tape = deque(tape)

    halt_state = actions.HALT

    return turing.TuringMachine(halt_state, tape, transition_table)