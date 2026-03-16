import random
import matplotlib.pyplot as plt
import networkx as nx

class FiniteSystem:
    def __init__(self, function_list: list[int], initial_state: int) -> None:
        '''
        Representation invariant:
        - All values of self._function_list are from 0 to len(function_list) - 1 inclusive
        - self._state is a natural from 0 to len(function_list) - 1 inclusive
        '''
        self._function_list = function_list

        self._state = initial_state
    
    def set_state(self, state: int) -> None:
        self._state = state
    
    def get_state(self) -> int:
        return self._state
    
    def __len__(self) -> int:
        return len(self._function_list)
    
    def __str__(self) -> str:
        return 'Function list: ' + str(self._function_list)
    
    def step(self) -> None:
        self._state = self._function_list[self._state]

    def step_once(self, state: int) -> int:
        return self._function_list[state]
    
    def step_nth(self, state: int, n: int) -> int:
        self.set_state(state)

        for _ in range(n):
            self.step()
        
        return self.get_state()
    
    def draw_graph(self) -> None:
        graph = nx.DiGraph()

        for i in range(len(self)):
            graph.add_edge(i, self.step_once(i))
        
        nx.draw(graph, with_labels = True)
        plt.show()

def rand_function_list(size: int) -> list[int]:
    result = []

    for _ in range(size):
        result.append(random.randrange(0, size))
    
    return result

def rand_translation(size: int) -> list[int]:
    return random.sample(range(size), size)

def orbit(system: FiniteSystem, initial_state: int, length: int) -> list[int]:
    result = []

    system.set_state(initial_state)

    for _ in range(length):
        result.append(system.get_state())
        system.step()
    
    return result

def first_duplicates(l: list):
    seen = {}

    for i, element in enumerate(l):
        if element in seen:
            return seen[element], i
        
        seen[element] = i
    
    return None

def cycle_start_end(system: FiniteSystem, initial_state: int) -> list[int]:
    max_cycle_len = len(system) + 1

    orbit_list = orbit(system, initial_state, max_cycle_len)

    return first_duplicates(orbit_list)

def is_permutation(l: list[int]) -> bool:
    return first_duplicates(l) is None

def maximum_steps(system: FiniteSystem, states: list[int]) -> list[int]:
    result = []

    for state in states:
        _, end = cycle_start_end(system, state)

        result.append(end)
    
    return result

def is_closed(system: FiniteSystem, states: list[int]):
    for state in states:
        output = system.step_once(state)

        if output not in states:
            return False
    
    return True

def is_simulation(system1: FiniteSystem, system2: FiniteSystem, steps: list[int], translation: list[int], sublist: list[int]) -> bool:
    '''
    Precondition:
    - len(steps) == len(sublist) == len(translation)
    - sublist is a sublist of the list of system1's states
    '''
    if not is_permutation(translation):
        return False
    
    if len(sublist) != len(system2):
        return False
    
    if not is_closed(system1, sublist):
        return False
    
    for i, state in enumerate(sublist):
        norm_output = sublist.index(system1.step_nth(state, steps[i]))
        output1 = translation[norm_output]
        output2 = system2.step_once(translation[i])

        if output1 != output2:
            return False
    
    return True

def rand_bounded(l: list[int]) -> list[int]:
    result = []

    for element in l:
        result.append(random.randrange(0, element + 1))
    
    return result

def find_simulation_random(system1: FiniteSystem, system2: FiniteSystem, n: int):
    '''
    Precondition: len(system1) >= len(system2)
    '''
    for _ in range(n):
        sublist = random.sample(range(len(system1)), len(system2))

        steps = rand_bounded(maximum_steps(system1, sublist))

        translation = rand_translation(len(system2))

        if is_simulation(system1, system2, steps, translation, sublist):
            return steps, translation, sublist
        
    return None

FiniteSystem(rand_function_list(100), 0).draw_graph()

found = None

print('-------------------------------------------')

while True:
    system1 = FiniteSystem(rand_function_list(5), 0)
    system2 = FiniteSystem(rand_function_list(5), 0)

    print(system1)
    print()
    print(system2)
    print()

    found = find_simulation_random(system1, system2, 100)
    
    if found is not None:
        if 0 in found[0]:
            continue

        print(f'Found: steps: {found[0]}; translation: {found[1]}; sublist: {found[2]}')
        print()

        system1.draw_graph()
        system2.draw_graph()

        break

    print()
    print('-------------------------------------------')