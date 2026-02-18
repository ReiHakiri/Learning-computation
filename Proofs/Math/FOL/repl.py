from interpreter import *
from display import *

print()

print('FOL proof maker\n')

while True:
    command = input()

    print()

    if command[:3] == 'run':
        try:
            with open('run_files/' + command[4:]) as file:
                file, n_args = find_n_args(file.readlines())

                file, context = find_context(file, n_args)

                proofs = separate_proofs(file)

                deductions = proofs_to_deductions(proofs, n_args, context)

                new_file_name = input('Enter name for latex file: ')

                print()

                deductions_to_latex(context, deductions, command[4:-4], new_file_name)

                latex_graph = deductions_to_display_latex(context, deductions)

                fig, _ = latex_display(latex_graph, 12, (18, 8))
                plt.show()

        except Exception as e:
            print(f'Python error: {e}')
    
    elif command == 'quit':
        break

    elif command == 'help':
        print('Command list:\n\nRun file: run <filename>\n\nQuit console: quit\n\nGet command list: help')

    else:
        print('Console error: invalid command')

    print()