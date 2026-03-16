import networkx as nx
import matplotlib.pyplot as plt

def around_graph(x, F: list, depth: int, previous = set(), seen = set()) -> set:
    if x in seen:
        return set()

    if depth == 0:
        return set()

    else:
        seen.add(x)

        for f in F:
            new_x = f(x)
            previous.add((x, new_x))

            previous = previous | around_graph(new_x, F, depth - 1, previous)

        return previous

def draw_graph(edge_set: set, layout = nx.spring_layout) -> None:
    graph = nx.DiGraph()

    for edge in edge_set:
        n1, n2 = edge

        graph.add_edge(n1, n2)

    pos = layout(graph)

    nx.draw(graph, pos, alpha = 0.5, node_size = 50, node_color = 'blue')
    plt.show()

collatz = lambda x: x // 2 if x % 2 == 0 else 3 * x + 1

lcg = lambda x: (23 * x + 5) % 52

mod_succ = lambda x: (x + 1) % 32

draw_graph(around_graph(5, [collatz, lcg, mod_succ], 5))