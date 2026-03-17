import networkx as nx
import matplotlib.pyplot as plt
from pyvis.network import Network
import webbrowser

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

def get_nx_graph(edge_set: set) -> nx.DiGraph:
    graph = nx.DiGraph()

    for edge in edge_set:
        n1, n2 = edge

        graph.add_edge(n1, n2)
    
    return graph

def draw_graph(edge_set: set, layout = nx.spring_layout) -> None:
    graph = get_nx_graph(edge_set)

    pos = layout(graph)

    nx.draw(graph, pos, alpha = 0.5, node_size = 100, node_color = 'blue', with_labels = True)
    plt.show()

def interact_graph(edge_set: set) -> None:
    graph = get_nx_graph(edge_set)

    net = Network(notebook = True, directed = True)
    net.from_nx(graph)

    net.show_buttons(filter_ = ['physics'])

    site_name = 'interactive_graph.html'
    net.show(site_name)

    webbrowser.open(site_name)

collatz = lambda x: x // 2 if x % 2 == 0 else 3 * x + 1

lcg = lambda x: (21 * x + 13) % 1000

mod_succ = lambda x: (x + 1) % 32

graph = around_graph(0, [collatz, lcg, mod_succ], 50)

draw_graph(graph)
interact_graph(graph)