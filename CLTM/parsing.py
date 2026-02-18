def clean_tokenizer(line: str) -> tuple[str]:
    return tuple(line.split(' '))

def tokenizer(file) -> tuple[int, list[int], tuple[tuple[int, tuple[str]]]]:
    result = []

    total_symbols = int(file.readline().strip())

    declaration = file.readline().strip()

    v_bounds = []

    if declaration != 'n':
        v_bounds = [int(v_bound) for v_bound in declaration.split(' ')]

    for line in file:
        n_tabs = (len(line) - len(line.lstrip(' '))) // 4

        line = line.strip()

        line = line.split('|')[0]

        if line == '': # Removes empty lines, but empty line needed for until operation, so will have to add these back in
            continue

        result.append((n_tabs, clean_tokenizer(line)))

    return total_symbols, v_bounds, tuple(result)

# print(tokenizer(open('test_and.txt')))