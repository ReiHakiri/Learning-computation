import compiler

print()

print('Convenient Language for Turing Machine compiler\n')

while True:
    command = input()

    print()

    if command[:3] == 'run':
        try:
            with open(command[4:]) as file:
                total_lines, v_bounds, transition_table = compiler.convert(file)

                transition_table = compiler.clean(transition_table, compiler.DEFAULT)

                tape = input('Enter tape: ')

                tape = tuple(int(cell) for cell in tape.split(' '))

                print()

                compiled_TM = compiler.get_TM(tape, transition_table, total_lines, v_bounds)

                print(compiled_TM.transition_table)

                print()

                steps = int(input('Enter steps: '))

                for output in compiled_TM.b_run(steps):
                    print(f'Output: {output} , halted: {compiled_TM.halted()}')

                    '''
                    print(compiler.actions.state_to_multi(compiled_TM.state, total_lines, v_bounds))
                    print(compiler.actions.state_to_multi(transition_table[compiled_TM.symbol][compiled_TM.state][1], total_lines, v_bounds))
                    print('\n\n')
                    '''

        except Exception as e:
            print(f'Python error: {e}')
    
    elif command == 'quit':
        break

    elif command == 'help':
        print('Command list:\n\nRun file: run <filename>\n\nQuit console: quit\n\nGet command list: help')

    else:
        print('Console error: invalid command')

    print()