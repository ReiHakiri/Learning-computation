from itertools import product

def multi_to_state(line_n: int, intermediate: int, v_values: list[int], total_lines: int, v_bounds: list[int]) -> int:
    result = line_n
    radix = total_lines

    result += intermediate * radix
    radix *= 3

    for v_value, v_bound in zip(v_values, v_bounds):
        if v_value >= v_bound:
            raise Exception('Variable value out of bounds')
        
        result += v_value * radix
        radix *= v_bound

    return result

def state_to_multi(state: int, total_lines: int, v_bounds: list[int]) -> tuple[int, int, list[int]]:
    line_n = state % total_lines

    state = (state - line_n) // total_lines

    intermediate = state % 3

    state = (state - intermediate) // 3

    v_values = []

    for v_bound in v_bounds:
        v_value = state % v_bound
        state = (state - v_value) // v_bound

        v_values.append(v_value)

    if state != 0:
        raise Exception('State out of bounds')

    return line_n, intermediate, v_values

def v_values_0(v_bounds: list[int]):
    result = []

    for _ in range(len(v_bounds)):
        result.append(0)

    return result

def all_v_values(v_bounds: list[int]) -> product:
    result = []

    for v_bound in v_bounds:
        result.append(range(v_bound))
        
    return product(*result)

def total_states(total_lines: int, v_bounds: list[int]) -> int:
    result = total_lines * 3

    for v_bound in v_bounds:
        result *= v_bound

    return result + 1

def blank_table(total_symbols: int, total_lines: int, v_bounds: list[int]) -> list[list[tuple[int, int, int]]]:
    result = []

    states = total_states(total_lines, v_bounds)

    for _ in range(total_symbols):
        row = []
        for _ in range(states):
            row.append(None)

        result.append(row)

    return result

HALT = -1

def add_halt(transition_table: list[list[int]], line_n: int, total_symbols: int, total_lines: int, v_bounds: list[int]) -> list[list[tuple[int, int, int]]]:
    for v_values in all_v_values(v_bounds):
        state = multi_to_state(line_n, 0, v_values, total_lines, v_bounds)

        for symbol in range(total_symbols):
                transition_table[symbol][state] = (symbol, HALT, 1)
    
    return transition_table

def add_repeat(transition_table: list[list[int]], line_n: int, total_symbols: int, total_lines: int, v_bounds: list[int]) -> list[list[tuple[int, int, int]]]:
    for v_values in all_v_values(v_bounds):
        state1 = multi_to_state(line_n, 0, v_values, total_lines, v_bounds)
        state2 = multi_to_state(line_n, 1, v_values, total_lines, v_bounds)
        state3 = multi_to_state(0, 0, v_values, total_lines, v_bounds) # Originally used v_values_0(v_bounds) instead of v_values

        for symbol1 in range(total_symbols):
            for symbol2 in range(total_symbols):
                transition_table[symbol1][state1] = (symbol1, state2, 1)
                transition_table[symbol2][state2] = (symbol2, state3, -1)
    
    return transition_table

def add_assignment(transition_table: list[list[int]], line_n: int, total_symbols: int, total_lines: int, v_bounds: list[int], i: int, value: int) -> list[list[tuple[int, int, int]]]:
    if value >= v_bounds[i]:
        raise Exception('Assignment value out of bounds')
    
    for v_values in all_v_values(v_bounds):
        state1 = multi_to_state(line_n, 0, v_values, total_lines, v_bounds)
        state2 = multi_to_state(line_n, 1, v_values, total_lines, v_bounds)

        if line_n + 1 >= total_lines:
            state3 = HALT
                
        else:
            v_values_c = list(v_values).copy()
            v_values_c[i] = value

            state3 = multi_to_state(line_n + 1, 0, v_values_c, total_lines, v_bounds)

        for symbol1 in range(total_symbols):
            for symbol2 in range(total_symbols):
                transition_table[symbol1][state1] = (symbol1, state2, 1)
                transition_table[symbol2][state2] = (symbol2, state3, -1)
    
    return transition_table

def add_if_variable(transition_table: list[list[int]], line_n: int, total_symbols: int, total_lines: int, v_bounds: list[int], i: int, value: int, p: int, q: int) -> list[list[tuple[int, int, int]]]:
    if value >= v_bounds[i]:
        raise Exception('Comparison value out of bounds')
    
    for v_values in all_v_values(v_bounds):
        state1 = multi_to_state(line_n, 0, v_values, total_lines, v_bounds)
        state2 = multi_to_state(line_n, 1, v_values, total_lines, v_bounds)
        state3 = multi_to_state(line_n + 1, 0, v_values, total_lines, v_bounds)

        state4 = multi_to_state(p - 1, 0, v_values, total_lines, v_bounds)
        state5 = multi_to_state(p - 1, 1, v_values, total_lines, v_bounds)
        state6 = multi_to_state(q, 0, v_values, total_lines, v_bounds)
        
        state7 = multi_to_state(p, 0, v_values, total_lines, v_bounds)
    
        for symbol1 in range(total_symbols):
            for symbol2 in range(total_symbols):
                if v_values[i] == value:
                    transition_table[symbol1][state1] = (symbol1, state2, 1)
                    transition_table[symbol2][state2] = (symbol2, state3, -1)

                else:
                    transition_table[symbol1][state1] = (symbol1, state2, 1)
                    transition_table[symbol2][state2] = (symbol2, state7, -1)
                
                transition_table[symbol1][state4] = (symbol1, state5, 1)
                transition_table[symbol2][state5] = (symbol2, state6, -1)
    
    return transition_table

def add_if_symbol(transition_table: list[list[int]], line_n: int, total_symbols: int, total_lines: int, v_bounds: list[int], m: int, p: int, q: int) -> list[list[tuple[int, int, int]]]:
    if m >= total_symbols:
        raise Exception('Comparison symbol out of bounds')
    
    for v_values in all_v_values(v_bounds):
        state1 = multi_to_state(line_n, 0, v_values, total_lines, v_bounds)
        state2_0 = multi_to_state(line_n, 1, v_values, total_lines, v_bounds)
        state2_1 = multi_to_state(line_n, 2, v_values, total_lines, v_bounds)
        state3 = multi_to_state(line_n + 1, 0, v_values, total_lines, v_bounds)

        state4 = multi_to_state(p - 1, 0, v_values, total_lines, v_bounds)
        state5 = multi_to_state(p - 1, 1, v_values, total_lines, v_bounds)
        state6 = multi_to_state(q, 0, v_values, total_lines, v_bounds)
        
        state7 = multi_to_state(p, 0, v_values, total_lines, v_bounds)

        for symbol1 in range(total_symbols):
            for symbol2 in range(total_symbols):
                if symbol1 == m:
                    transition_table[symbol1][state1] = (symbol1, state2_0, 1)
                    transition_table[symbol2][state2_0] = (symbol2, state3, -1)

                else:
                    transition_table[symbol1][state1] = (symbol1, state2_1, 1)
                    transition_table[symbol2][state2_1] = (symbol2, state7, -1)

                transition_table[symbol1][state4] = (symbol1, state5, 1)
                transition_table[symbol2][state5] = (symbol2, state6, -1)
    
    return transition_table

def add_change(transition_table: list[list[int]], line_n: int, total_symbols: int, total_lines: int, v_bounds: list[int], m: int, d: int) -> list[list[tuple[int, int, int]]]:
    for v_values in all_v_values(v_bounds):
        state1 = multi_to_state(line_n, 0, v_values, total_lines, v_bounds)

        if line_n + 1 >= total_lines:
            state2 = HALT

        else:
            state2 = multi_to_state(line_n + 1, 0, v_values, total_lines, v_bounds)

        for symbol in range(total_symbols):
            transition_table[symbol][state1] = (m, state2, d)
    
    return transition_table

def add_overwrite(transition_table: list[list[int]], line_n: int, total_symbols: int, total_lines: int, v_bounds: list[int], m: int) -> list[list[tuple[int, int, int]]]:
    for v_values in all_v_values(v_bounds):
        state1 = multi_to_state(line_n, 0, v_values, total_lines, v_bounds)
        state2 = multi_to_state(line_n, 1, v_values, total_lines, v_bounds)

        if line_n + 1 >= total_lines:
            state3 = HALT
                
        else:
            state3 = multi_to_state(line_n + 1, 0, v_values, total_lines, v_bounds)
        
        for symbol1 in range(total_symbols):
            for symbol2 in range(total_symbols):
                transition_table[symbol1][state1] = (m, state2, 1)
                transition_table[symbol2][state2] = (symbol2, state3, -1)

    return transition_table

def add_move(transition_table: list[list[int]], line_n: int, total_symbols: int, total_lines: int, v_bounds: list[int], d: int) -> list[list[tuple[int, int, int]]]:
    for v_values in all_v_values(v_bounds):
        state1 = multi_to_state(line_n, 0, v_values, total_lines, v_bounds)

        if line_n + 1 >= total_lines:
            state2 = HALT

        else:
            state2 = multi_to_state(line_n + 1, 0, v_values, total_lines, v_bounds)

        for symbol in range(total_symbols):
            transition_table[symbol][state1] = (symbol, state2, d)
    
    return transition_table

def add_until_variable(transition_table: list[list[int]], line_n: int, total_symbols: int, total_lines: int, v_bounds: list[int], i: int, value: int, p: int) -> list[list[tuple[int, int, int]]]:
    if value >= v_bounds[i]:
        raise Exception('Comparison value out of bounds')
    
    for v_values in all_v_values(v_bounds):
        state1 = multi_to_state(line_n, 0, v_values, total_lines, v_bounds)
        state2 = multi_to_state(line_n, 1, v_values, total_lines, v_bounds)
        state3 = multi_to_state(line_n + 1, 0, v_values, total_lines, v_bounds)

        state4 = multi_to_state(p, 0, v_values, total_lines, v_bounds)
        state5 = multi_to_state(p, 1, v_values, total_lines, v_bounds)
        
        if p + 1 >= total_lines:
            state6 = HALT
        
        else:
            state6 = multi_to_state(p + 1, 0, v_values, total_lines, v_bounds)

        for symbol1 in range(total_symbols):
            for symbol2 in range(total_symbols):
                if v_values[i] == value:
                    transition_table[symbol1][state1] = (symbol1, state2, 1)
                    transition_table[symbol2][state2] = (symbol2, state6, -1)

                else:
                    transition_table[symbol1][state1] = (symbol1, state2, 1)
                    transition_table[symbol2][state2] = (symbol2, state3, -1)

                transition_table[symbol1][state4] = (symbol1, state5, 1)
                transition_table[symbol2][state5] = (symbol2, state1, -1)

    return transition_table

def add_until_symbol(transition_table: list[list[int]], line_n: int, total_symbols: int, total_lines: int, v_bounds: list[int], m: int, p: int) -> list[list[tuple[int, int, int]]]:
    if m >= total_symbols:
        raise Exception('Comparison symbol out of bounds')
    
    for v_values in all_v_values(v_bounds):
        state1 = multi_to_state(line_n, 0, v_values, total_lines, v_bounds)
        state2_0 = multi_to_state(line_n, 1, v_values, total_lines, v_bounds)
        state2_1 = multi_to_state(line_n, 2, v_values, total_lines, v_bounds)
        state3 = multi_to_state(line_n + 1, 0, v_values, total_lines, v_bounds)

        state4 = multi_to_state(p, 0, v_values, total_lines, v_bounds)
        state5 = multi_to_state(p, 1, v_values, total_lines, v_bounds)
        
        if p + 1 >= total_lines:
            state6 = HALT
        
        else:
            state6 = multi_to_state(p + 1, 0, v_values, total_lines, v_bounds)

        for symbol1 in range(total_symbols):
            for symbol2 in range(total_symbols):
                if symbol1 == m:
                    transition_table[symbol1][state1] = (symbol1, state2_0, 1)
                    transition_table[symbol2][state2_0] = (symbol2, state6, -1)

                else:
                    transition_table[symbol1][state1] = (symbol1, state2_1, 1)
                    transition_table[symbol2][state2_1] = (symbol2, state3, -1)

                transition_table[symbol1][state4] = (symbol1, state5, 1)
                transition_table[symbol2][state5] = (symbol2, state1, -1)

    return transition_table