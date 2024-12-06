import itertools
from sage.all import *
from sage.graphs.generic_graph_pyx import SubgraphSearch


#makes exponential distance matrix of graph G given value of q
def exp_dist(G,q):
    n=G.num_verts()
    M=[]
    distances=G.distance_all_pairs()
    for i in range(n):
        row=[0]*G.order()
        for j in distances[i]:
            row[j]=(q^distances[i][j])
        M.append(row)
    return matrix(M)

#given a list of graphs and matrix type, finds the ones that are cospectral
def find_cospectral_exp(graph_list, n=None):
    # n is the (max) number of vertices for a graph in graph_list
    poly = {}

    # leave n as None if you want to do things purely symbolically
    if n is None:
        for G in graph_list:
            f = exp_dist(G,q).characteristic_polynomial()
            if f in poly:
                poly[f].append(G.canonical_label().graph6_string())
            else:
                poly[f]=[G.canonical_label().graph6_string()]
    else:
        # check the charpoly from n+1 distinct q-values
        # I'm sure this is more checks than necessary but I didn't want to think too hard
        q_vals = [1/i for i in range(1, n+2)]
        for G in graph_list:
            f_tup = tuple([exp_dist(G,q_val).characteristic_polynomial() for q_val in q_vals])
            if f_tup in poly:
                poly[f_tup].append(G.canonical_label().graph6_string())
            else:
                poly[f_tup]=[G.canonical_label().graph6_string()]
    mates=[]
    for M in poly:
        if len(poly[M])>1:
            mates.append(poly[M])
            
    pairwise_mates = []
    for pair in mates:
        pairwise_mates.extend(list(itertools.combinations(pair, 2)))
    return pairwise_mates

#get all regular graphs on n vertices
def get_regular_graphs(n):
    regular_graphs = []
    for G in graphs.nauty_geng(str(n)):
        if G.degree_sequence()[0] == G.degree_sequence()[-1] and G.degree_sequence()[-1] != 0:
            regular_graphs.append(G.canonical_label().graph6_string())
    return(regular_graphs)


#given an order n, returns all possible graphs that A could be (this includes our new A_i construction)
def get_possible_A_graphs(n):
    possible_A_graphs = []
    
  # Get all regular graphs on at least 4 vertices. We pick 4 because on 2, pairs following our construction will always be isomorphic
    for i in range(4, n+1):
        possible_A_graphs += get_regular_graphs(i)
        
    # Filter to keep only connected graphs that qualify
    valid_graphs = []
    for g in possible_A_graphs:
        graph = Graph(g)
        if graph.is_connected():  # Only consider connected graphs
            # Check if the graph is at least |Ai|/2 regular and |Ai| is even
            if graph.degree_sequence()[0] >= graph.order() / 2 and graph.order() % 2 == 0:
                valid_graphs.append(Graph(g))

    return valid_graphs

#function that outputs a list of edges where the edge's incident vertices share a neighborhood in the input A
def get_corollary_edges(G, G_minus_A, A_nodes):
    A_node_set = set(A_nodes)
    
    list_corollary_edges = []
    
    #iterate over all pairs of vertices in G_minus_A (these are the B_i's)
    for b1 in G_minus_A:
        for b2 in G_minus_A:
            if G.has_edge(b1,b2):
                #get neighborhoods of b1 and b2
                b1_nbhd_A = set(G.neighbors(b1)).intersection(A_node_set)
                b2_nbhd_A = set(G.neighbors(b2)).intersection(A_node_set)
                
                #if b1 and b2 share a neighbor in A, means we can remove this edge
                if b1_nbhd_A.intersection(b2_nbhd_A):
                    list_corollary_edges.append((b1,b2))
    
    return list_corollary_edges

#given a graph and a potential A, finds if the vertices in the B_i's that are connected to half of vertices are same half
def check_half_adjacency_consistency(G, A_nodes):
    #G_minus_A is the collection of all B_i's
    G_minus_A = G.copy()
    G_minus_A.delete_vertices(A_nodes)
    
    #get edges that can be removed from corollary 2.6
    corollary_edges = get_corollary_edges(G, G_minus_A, A_nodes)
    
    #remove corollary 2.6 edges
    G_minus_A.delete_edges(corollary_edges)
    
    components = G_minus_A.connected_components_subgraphs()

    A_node_set = set(A_nodes)
    A_size_half = len(A_nodes) // 2

    #these lists are used to find the edges that will switch between G and its construction pair.
    missing_edges = []
    existing_edges = []
    
    #iterate over each B_i
    for B_i in components:
        half_adjacent_nodes = []
        adjacency_patterns = {}

        #for each B_i, record the neighborhood of each b that is also in A
        for node in B_i:
            neighbors_in_A = set(G.neighbors(node)).intersection(A_node_set)
            if len(neighbors_in_A) == A_size_half:
                half_adjacent_nodes.append(node)
                adjacency_patterns[node] = neighbors_in_A

        #make sure that the list of vertices connected to half of A is nonempty
        if len(half_adjacent_nodes) >= 1:
            #check that all nodes in half_adjacent_nodes share the same adjacency pattern
            first_pattern = adjacency_patterns[half_adjacent_nodes[0]]
            for node in half_adjacent_nodes[1:]:
                #return empty lists if inconsistent neighborhoods (this is equivalent to returning false)
                if adjacency_patterns[node] != first_pattern:
                    return [], [], []

            #collect existing and missing edges between half_adjacent_nodes and A_nodes
            for node in half_adjacent_nodes:
                for neighbor in A_node_set:
                    #if the edge exists in the graph
                    if G.has_edge(node, neighbor):
                        existing_edges.append((node, neighbor))
                    #if the edge is missing in the graph
                    else:
                        missing_edges.append((node, neighbor))
                        
    #Return all lists in a tuple
    return(missing_edges, existing_edges, corollary_edges)

#given a pair of cospectral graphs on n vertices, checks if they follow our construction
def validate_graph(graph, graph2, n):
    #find all possible subgraphs A
    candidate_As = get_possible_A_graphs(n)
    
    #iterate over possible As
    for A in candidate_As:
        
        #for each possible A, find where it appears as a subgraph in "graph". Iterate over potential subgraphs
        for mapping in graph.subgraph_search_iterator(A, induced=True):
            #get the vertices in G corresponding to the subgraph isomorphic to A
            subgraph_vertices = mapping
            
            #check half-adjacency consistency with this particular subgraph
            list_missing_edges, list_existing_edges, corollary_edges = check_half_adjacency_consistency(graph, subgraph_vertices)
            
            #if half-adjacency is valid, switch the necessary edges between A and B to get the cospectral pair from our construction
            if list_missing_edges != [] and list_existing_edges != []:
                construction_pair = graph.copy()
                construction_pair.delete_edges(list_existing_edges)
                construction_pair.add_edges(list_missing_edges)
                construction_pair.add_edges(corollary_edges)
                
                #if the constructed graph is isomorphic to the second input graph, print true
                if construction_pair.is_isomorphic(graph2):
                    print("follows")
                    return True
    
    #if run through all code and doesnt find a constructed graph that works, then the input pair doesn't follow our construction
    print("doesnt follow")
    return False

#Run instance when n=7
n=7
cospec_on_n = find_cospectral_exp(graphs.nauty_geng(str(n)), n)
constructed_pairs = []

for pair in cospec_on_n:
    if validate_graph(Graph(pair[0]), Graph(pair[1]), n):
        constructed_pairs.append(pair)

print(len(cospec_on_n))
print(len(constructed_pairs))
