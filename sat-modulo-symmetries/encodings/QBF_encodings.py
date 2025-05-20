from pysms.qcir_graph_builder import *

global n, m, PosV
n = 6
m = 8
PosV = 1


def pos(i):
    if(i < PosV):
        return 2*i
    return i + PosV 

def neg(i):
    if(i < PosV):
        return 2*i + 1
    return 2*n + PosV - i - 1

def cpos(i):
    return 2*n + i

# every clasue have not to be connected
def F1(builder: GraphEncodingBuilder, n, m):
    for i, j in combinations(list(range(m)), 2) :     
        builder.addExistentialGate(-builder.var_edge(cpos(i), cpos(j)))
    return

# every literals have to appear at least once
def F2(builder: GraphEncodingBuilder, n, m):
    for sign in [pos, neg] :
        for i in range(n) :
            clause = []
            for j in range(m) :
                clause.append(builder.var_edge(sign(i), cpos(j)))
            builder.addExistentialGate(OrGate(builder.id(), clause))

# no True Clause
def F3(builder: GraphEncodingBuilder, n, m):
    for i in range(n):
        for j in range(m):
            clause = [
                -builder.var_edge(pos(i),    cpos(j)),
                -builder.var_edge(neg(i),    cpos(j)),
            ]
            builder.addExistentialGate(OrGate(builder.id(), clause))

# set the degree of clauses to k
def setClauseDegreeK(builder:GraphEncodingBuilder, n, m, k): # F5
    for j in range(m):
        outputGate = AndGate(builder.id(), [])
        variables = [builder.var_edge(i, cpos(j)) for i in range(2*n)]
        #seqCounter(variables, k, builder, outputGate, k, k)
        seqCounter(variables, k, builder, outputGate, k, 1) # use it for <=k - cnf formula
        builder.addExistentialGate(outputGate)

# set the maximum number of Occurence to k 
def setMaxVarOccurenceS(builder:GraphEncodingBuilder, n, m, s): # F4v
    for i in range(n):
        outputGate = AndGate(builder.id(), [])
        variables = []
        variables.extend([builder.var_edge(pos(i), cpos(j)) for j in range(m)])
        variables.extend([builder.var_edge(neg(i), cpos(j)) for j in range(m)])
        seqCounter(variables, s, builder, outputGate, s, 0)
        builder.addExistentialGate(outputGate)

def setMaxVarOccurencePQ(builder:GraphEncodingBuilder, n, m, p, q): # F4pq
    for i in range(n):
        outputGate = AndGate(builder.id(), [])
        variables = []
        variables.extend([builder.var_edge(pos(i), cpos(j)) for j in range(m)])
        seqCounter(variables, p, builder, outputGate, p, 0)
        builder.addExistentialGate(outputGate)
    for i in range(n):
        outputGate = AndGate(builder.id(), [])
        variables = []
        variables.extend([builder.var_edge(neg(i), cpos(j)) for j in range(m)])
        seqCounter(variables, q, builder, outputGate, q, 0)
        builder.addExistentialGate(outputGate)


# no blocked clauses 
def F6(builder: GraphEncodingBuilder, n, m):
    psi = {} # psi of F6
    
    for i in range(n):
        for j in range(m):
            for j_p in range(m):
                variables = []
                for i_p in range(n):
                    if(i_p == i): continue
                    variables.append(OrGate(builder.id(), [-builder.var_edge(pos(i_p), cpos(j)), -builder.var_edge(neg(i_p), cpos(j_p) )]))
                    variables.append(OrGate(builder.id(), [-builder.var_edge(neg(i_p), cpos(j)), -builder.var_edge(pos(i_p), cpos(j_p) )]))
                psi[(i, j, j_p)] = AndGate(builder.id(), variables)

    
    phi = [] # phi of F6

    sf = [pos, neg]

    for sign in range(2):
        for i in range(n):
            for j in range(m):
                variables = []
                for j_p in range(m):
                    if(j == j_p): continue
                    variables.append(AndGate(builder.id(), [builder.var_edge(sf[ (sign+1) %2 ](i), cpos(j_p) ), psi[(i, j, j_p)]])) 
                phi.append(OrGate(builder.id(), [-builder.var_edge(sf[sign](i), cpos(j)), OrGate(builder.id(), variables)]))
            builder.addExistentialGate(AndGate(builder.id(), phi))
    pass


# minimal constrains
def F7(builder:GraphEncodingBuilder, n, m):
    for i in range(n):
        builder.addExistentialGate(builder.var_edge(pos(i),neg(i)))
        for i_p in range(n):
            if(i != i_p):
                builder.addExistentialGate(-builder.var_edge(pos(i), neg(i_p)))
    
    for i, i_p in combinations(list(range(n)), 2):
        builder.addExistentialGate(-builder.var_edge(pos(i), pos(i_p)))
        builder.addExistentialGate(-builder.var_edge(neg(i), neg(i_p)))
        pass

# unsatisfiable
def checkUNSAT(builder:GraphEncodingBuilder, n, m):
    sumnm = AndGate(builder.id(), [])

    truth = [builder.id() for _ in range(n)]

    for j in range(m):
        gate = OrGate(builder.id(), [])
        for sign in [-1, 1]:
            for i in range(n):
                if(sign == -1): 
                    gate.appendToInput(AndGate(builder.id(), [-truth[i], builder.var_edge(neg(i), cpos(j))]))
                else:
                    gate.appendToInput(AndGate(builder.id(), [truth[i], builder.var_edge(pos(i), cpos(j))]))
        sumnm.appendToInput(gate)

    output = NegatedGate(sumnm)
    '''
    #debugging 
    print("truth: " , truth) 
    edgevars = builder.getFreeVariables()
    print("encodingvar: ", [v for v in GraphEncodingBuilder.getVariables(output) if v not in edgevars])
    '''
    builder.addUniversalGate(output)


def main():
    global PosV # improved encoding


    k = 3
    s = 4

    p = 1
    q = 3


    # improved encoding
    for v in range(1, n+1) :
        PosV = v
        Lo = n-v
        print("V: ", v)

        builder = GraphEncodingBuilder(2*n + m, directed=False)
        builder.paramsSMS["cutoff"] = 0
        builder.paramsSMS["frequency"] = 30
        #builder.paramsSMS["initial-partition"] = f"{2*n} {m}" # basic encoding
        builder.paramsSMS["initial-partition"] = " ".join(["1" for _ in range(2*PosV + Lo)]) + f" {2*n - 2*PosV - Lo} {m}"  # set the partitions of mincheck


        F1(builder, n, m)
        F2(builder, n, m)
        F3(builder, n, m)

        setClauseDegreeK(builder, n, m, k) # F5
        #setMaxVarOccurenceS(builder, n, m, s) # F4v
        setMaxVarOccurencePQ(builder, n, m, p, q) # F4l

        F6(builder, n, m)
        F7(builder, n, m)

        checkUNSAT(builder, n, m)
        
        builder.solve(allGraphs=False)

if __name__ == "__main__":
    main()