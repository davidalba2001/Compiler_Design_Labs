from cmp.pycompiler import Symbol
from cmp.pycompiler import NonTerminal
from cmp.pycompiler import Terminal
from cmp.pycompiler import EOF
from cmp.pycompiler import Sentence, SentenceList
from cmp.pycompiler import Epsilon
from cmp.pycompiler import Production
from cmp.pycompiler import Grammar
from cmp.utils import ContainerSet
from cmp.utils import pprint, inspect

G = Grammar()
E = G.NonTerminal('E', True)
T,F,X,Y = G.NonTerminals('T F X Y')
plus, minus, star, div, opar, cpar, num = G.Terminals('+ - * / ( ) num')

E %= T + X
X %= plus + T + X | minus + T + X | G.Epsilon
T %= F + Y
Y %= star + F + Y | div + F + Y | G.Epsilon
F %= num | opar + E + cpar

def compute_local_first(firsts, alpha):
    first_alpha = ContainerSet()
    
    try:
        alpha_is_epsilon = alpha.IsEpsilon
    except:
        alpha_is_epsilon = False

    if alpha_is_epsilon:
        first_alpha.set_epsilon()

    else:      
        for symbol in alpha:
            if not firsts[symbol].contains_epsilon:
                first_alpha.set_epsilon(False)   
                first_alpha.update(firsts[symbol])
                break
            else:
                first_alpha.hard_update(firsts[symbol])

    return first_alpha

# Computes First(Vt) U First(Vn) U First(alpha)
# P: X -> alpha
def compute_firsts(G:Grammar):
    firsts = {}
    change = True
    
    # init First(Vt)
    for terminal in G.terminals:
        firsts[terminal] = ContainerSet(terminal)
        
    # init First(Vn)
    for nonterminal in G.nonTerminals:
        firsts[nonterminal] = ContainerSet()
    
    while change:
        change = False
        
        # P: X -> alpha
        for production in G.Productions:
            X = production.Left
            alpha = production.Right
            
            # get current First(X)
            first_X = firsts[X]
                
            # init First(alpha)
            try:
                first_alpha = firsts[alpha]
            except KeyError:
                first_alpha = firsts[alpha] = ContainerSet()
            
            # CurrentFirst(alpha)???
            local_first = compute_local_first(firsts, alpha)
            
            # update First(X) and First(alpha) from CurrentFirst(alpha)
            change |= first_alpha.hard_update(local_first)
            change |= first_X.hard_update(local_first)
                    
    # First(Vt) + First(Vt) + First(RightSides)
    return firsts

from typing import Dict,Any

def compute_follows(G, firsts):
    follows: Dict[Any, ContainerSet] = {}
    change = True

    local_firsts = {}
    
    for nonterminal in G.nonTerminals:
        follows[nonterminal] = ContainerSet()
    follows[G.startSymbol] = ContainerSet(G.EOF)

    while change:
        change = False

        # P: X -> alpha
        for production in G.Productions:
            X = production.Left
            alpha = production.Right

            follow_X = follows[X]

            for (i,symbol) in enumerate(alpha):
                if symbol.IsNonTerminal:
                    local_firsts = compute_local_first(firsts, alpha[i+1:])
                    if not local_firsts.contains_epsilon:
                        change |= follows[symbol].update(local_firsts)
                    else:
                        change |= follows[symbol].update(local_firsts)
                        change |= follows[symbol].update(follow_X)
            
            # Handle the case when the last symbol is a non-terminal
            if alpha and alpha[-1].IsNonTerminal:
                change |= follows[alpha[-1]].update(follow_X)

    # Follow(Vn)
    return follows

class LL1GrammarException(Exception):
    pass

def build_parsing_table(G: Grammar, firsts, follows):
    # init parsing table
    M = {}
    
    # P: X -> alpha
    for production in G.Productions:
        X = production.Left
        alpha = production.Right

        try:
            alpha_is_epsilon = alpha.IsEpsilon
        except AttributeError:
            alpha_is_epsilon = False

        if not alpha_is_epsilon:
            for term in firsts[alpha]:
                if (X, term) in M:
                    raise LL1GrammarException(f"Grammar is not LL(1): Conflict at non-terminal {X} with terminal {term}")
                M[X, term] = [production]
        else:
            for term in follows[X]:
                if (X, term) in M:
                    raise LL1GrammarException(f"Grammar is not LL(1): Conflict at non-terminal {X} with terminal {term}")
                M[X, term] = [production]
        
    return M

def metodo_predictivo_no_recursivo(G:Grammar, M=None, firsts=None, follows=None):
    
    # checking table...
    if M is None:
        if firsts is None:
            firsts = compute_firsts(G)
        if follows is None:
            follows = compute_follows(G, firsts)
        M = build_parsing_table(G, firsts, follows)
    
    
    # parser construction...
    def parser(w):
        
        # init:
        stack = [G.EOF,G.startSymbol]
        index = 0
        left_parse = []

        while True:
            top = stack.pop()
            term = w[index]
            
            if top == G.EOF:
                if term == G.EOF:
                    break  # Successful parsing
                else:
                    raise ValueError("Parsing error: input not fully consumed at EOF")
            
            elif top in G.terminals:
                if top == term:
                    index += 1
                else:
                    raise ValueError(f"Parsing error: expected {top} but found {term}")
            
            
            elif top in G.nonTerminals:
                if (top,term) in M:
                    production = M[(top, term)][0]
                    left_parse.append(production)
                    for symbol in reversed(production.Right):
                        if not symbol.IsEpsilon:
                            stack.append(symbol)
                else:
                    raise ValueError(f"Parsing error: no production for ({top}, {term}) in parsing table")
            else:
                raise ValueError(f"Parsing error: unrecognized symbol {top} on stack")
        
        if index != len(w) - 1:  # Ensure the input is fully consumed
            raise ValueError("Parsing error: input not fully consumed")
        
        # left parse is ready!!!
        return left_parse
    
    # parser is ready!!!
    return parser

parser = metodo_predictivo_no_recursivo(G)
left_parse = parser([num, star, num, star, num, plus, num, star, num, plus, num, plus, num, G.EOF])

assert left_parse == [ 
   Production(E, Sentence(T, X)),
   Production(T, Sentence(F, Y)),
   Production(F, Sentence(num)),
   Production(Y, Sentence(star, F, Y)),
   Production(F, Sentence(num)),
   Production(Y, Sentence(star, F, Y)),
   Production(F, Sentence(num)),
   Production(Y, G.Epsilon),
   Production(X, Sentence(plus, T, X)),
   Production(T, Sentence(F, Y)),
   Production(F, Sentence(num)),
   Production(Y, Sentence(star, F, Y)),
   Production(F, Sentence(num)),
   Production(Y, G.Epsilon),
   Production(X, Sentence(plus, T, X)),
   Production(T, Sentence(F, Y)),
   Production(F, Sentence(num)),
   Production(Y, G.Epsilon),
   Production(X, Sentence(plus, T, X)),
   Production(T, Sentence(F, Y)),
   Production(F, Sentence(num)),
   Production(Y, G.Epsilon),
   Production(X, G.Epsilon),
]