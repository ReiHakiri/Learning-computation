from parsing import *
from deduction import *
import matplotlib.pyplot as plt

def latex_display(s: str, text_size: int, fig_size: tuple[int, int]) -> tuple:
    fig, ax = plt.subplots(figsize = fig_size)

    ax.text(0.5, 0.5, s, fontsize = text_size, ha = 'center', va = 'center')
    ax.axis('off')

    return fig, ax

def deductions_to_display_latex(context: tuple, deductions: tuple) -> str:
    result = r'$A = \{' + ', '.join(tree_to_latex(axiom) for axiom in context) + r'\}$'

    for i, deduction in enumerate(deductions):
        result += '\n\nProof ' + str(i + 1) + '\n\n'

        for formula in deduction:
            result += r'$A \vdash ' + tree_to_latex(formula) + '$' + '\n'
    
    return result