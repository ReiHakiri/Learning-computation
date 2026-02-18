from collections import deque

class TuringMachine:
    def __init__(self, halt_state: int, tape: deque[int], transition_table: tuple[tuple[tuple[int, int, int], ...], ...]):
        self.halt_state = halt_state

        self.tape = tape
        self.transition_table = transition_table

        self.pointer = 0
        self.symbol = self.tape[self.pointer]
        self.state = 0

    def step(self) -> tuple[bool, deque[int]]:
        if self.state == self.halt_state:
            return True, self.tape.copy()
        
        next_symbol, self.state, next_direction = self.transition_table[self.symbol][self.state]

        self.tape[self.pointer] = next_symbol

        if self.pointer == 0 and next_direction == -1:
            self.tape.appendleft(0)

        else:
            self.pointer += next_direction

            if self.pointer == len(self.tape):
                self.tape.append(0)

        self.symbol = self.tape[self.pointer]

        return False, self.tape.copy()
    
    def run(self):
        halt = False

        while not halt:
            halt, tape = self.step()

            yield tape

    def b_run(self, steps: int):
        halt = False
        index = 0

        while not halt and index < steps:
            halt, tape = self.step()

            index += 1

            yield tape
    
    def halted(self) -> bool:
        return self.state == self.halt_state

'''
from itertools import product

transition_table = (
    ((1, 1, 1), (0, 0, 1), (0, 4, -1), (0, 4, -1), (0, 3, -1), (1, 1, 1), (0, 7, -1), (1, 11, -1), (1, 9, -1),
     (0, 12, 1), (1, 6, -1), (0, 10, 1), (0, 14, -1), (0, 12, 1), (1, 8, -1), (0, 16, 1), (0, 18, 1), (0, 14, 1)),
    ((1, 2, 1), (1, 0, 1), (1, 8, -1), (1, 5, -1), (0, 3, -1), (0, 3, -1), (1, 8, -1), (1, 6, -1), (1, 6, -1), 
     (1, 14, 1), (1, 11, 1), (1, 10, 1), (1, 13, 1), (1, 12, 1), (0, 15, 1), (1, 14, 1), (0, 17, 1), (0, 0, 1))
)

# From U2,18 of https://dna.hamilton.ie/assets/dw/NearyWoodsMCU07.pdf

u_2_18 = lambda tape: TuringMachine((0, 1), 18, tape, transition_table)

def b_min(tape: deque[int], steps: int) -> deque[int]:
    for l in range(1, len(tape) + 1):
        for c_tape in product([0, 1], repeat = l):
            c_tape = deque(c_tape)

            if c_tape == tape:
                return c_tape

            utm = u_2_18(c_tape)

            for next_tape in utm.b_run(steps):
                if next_tape == tape:
                    return c_tape
                
min_l = []

for l in range(100, 1001):
    steps = 1000

    for tape in product([0, 1], repeat = l):
        tape = deque(tape)

        min_tape = b_min(tape, steps)
        l_min_tape = len(min_tape)

        min_l.append(l_min_tape)

        print(f'Tape: {tape} , min tape: {min_tape} , length diff: {len(tape) - l_min_tape}')
'''