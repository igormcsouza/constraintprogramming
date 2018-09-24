
# coding: utf-8

# In[122]:


# Algoritmo de Balas - PPR para resolver problemas binários
# Igor Souza (347208) e Rodrigo Meneses (376176)

# First -> Import
import math


# In[123]:


#Second -> Read

file = open('problema.txt', 'r')
n = int(file.readline())  # numero de variáveis
m = int(file.readline())  # numero de restrições

c = file.readline().split()  # coeficientes da função objetiva
c = [int(item) for item in c]
c.insert(0, 0)
print(c)

b = file.readline().split()  # Lado esquedo da função
b = [int(item) for item in b]
print(b)

A = list()  # restrições
for i in range(m):
    A.append(file.readline().split())
    A[i] = [int(item) for item in A[i]]
    A[i].insert(0, 0)

print(A)

file.close()


# In[124]:


# Global Variables e outras Declarações ----------------------------------------------------------------#
J = list()  # Lista de variaveis que serão trabalhadas no algoritmo
N1 = list()
N2 = list()

currentZ = math.inf  # Função objetiva atual
Zmin = currentZ  # Melhor função objetiva

Jvar = list()  # Lista de variaveis de J já fixadas
Avar = list()  # Lista de variaveis de J que não ajudam na viabilidade
Bvar = list()  # Lista de variaveis de J que atrapalham
Ccons = list()  # Restrições que não podem ser satisfeitas
S = list()  # Variáveis de Folga
restricoesVioladas = list()

N = list(range(1, n + 1))  # Total de variáveis de decisão
X = ['*'] * (n + 1)  # Variaveis de decisao, 0, 1 ou '*' (livre) -------------------------------------#

print(N)
print(X)
print(Zmin)


# In[125]:


# Construimos o arquivo partindo do presuposto que é inviável, caso contrário o algoritmo modifica ---#
file = open('solucao.txt', 'w')
file.write("inviavel")
print("File create succesfully!!")
file.close()
# ----------------------------------------------------------------------------------------------------#


# In[126]:


def writeInFile(a, B): #Função para escrever o resultado, o melhor já alcançado
    # Iniciando o arquivo para fazer o registro da solução
    file = open('solucao.txt', 'w')
    for i in B:
        file.write(f'{i}')
    file.write("\n")
    file.write(f'{a}')
    file.close()
    return


# In[127]:


# INICIO DO TESTE DE BALAS

def goBalas(doA, doB):
    
    global Jvar  # Sem modificar o J, vamos guardar os elementos do mesmo
    Jvar.clear()
    Jvar = [abs(var[0]) for var in J]
    
    # ------------------------------------------------###------------------------------------------------ #

    # vdA = N / vdJ que em toda restrição violada os A[i][j] são maiores que 0
    global Avar, N1, S, restricoesVioladas
    Avar.clear()

    S = [0] * m  # S[i] variavel de folga da restrição i
    s = 0
    for i in range(m):  # Primeiro, resolver o S[i] com as variaveis de J que já temos
        for j in Jvar:
            s += A[i][j] * X[j]
        S[i] = b[i] - s
        s = 0

    # Segundo, identificar quais restrições estão violadas e guardar seus indices
    restricoesVioladas = [i for i in range(m) if S[i] < 0]

    # variaveisDeTeste = N / J
    variaveisDeTeste = [i for i in N if i not in Jvar]

    for i in variaveisDeTeste:  # Terceiro, conferir se variavel ajuda na viabilidade
        bad = True
        for j in restricoesVioladas:
            if A[j][i] < 0:
                bad = False
                break
        if bad:
            Avar.append(i)  # Adicionar variaveis que não ajudam

    N1 = [i for i in N if i not in Jvar or i in Avar]

    passA = (len(N1) == 0)
    
    # ------------------------------------------------###------------------------------------------------ #

    # vdB = N / (J U A), são variaveis cuja o Z atual + o custo no vetor C é maior que Zmin, ou seja
    # Botar essas variáveis em 1 não vai ajudar a encontrar uma solução melhor.
    # variaveisDeTeste = N / (J U A) # Primeiro, identificar variaveis candidatas ao teste

    global Bvar, N2
    Bvar.clear()

    localFO = funcObj()
    for i in N1:  # Segundo, testar a influencia dessa variavel na funcao objetiva
        if localFO + c[i] > Zmin:
            Bvar.append(i)  # Variaveis que atrapalham

    N2 = [i for i in N1 if i not in Bvar]

    passB = (len(N2) == 0)
    
    # ------------------------------------------------###------------------------------------------------ #

    # São restrições violadas cuja melhor situação das variaveis livres não resolve a inviabilidade
    global Ccons
    Ccons.clear()
    s = 0

    for i in restricoesVioladas:
        for j in N2:
            s += min(0, A[i][j])
        if s > S[i]:
            Ccons.append(i)  # Restrições que não podem ser satisfeitas.
            
    # ------------------------------------------------###------------------------------------------------ #

    if len(Ccons) != 0 or (doA and passA) or (doB and passB):
        return True
    return False

# FIM TESTES DE BALAS


# In[128]:


def atualizaX():
    # Preencher X
    global X  # Para modificar variáveis globais, tem que fazer isso
    X.clear()
    X = ['*'] * (n + 1)
    X[0] = 0
    for i in J:
        if i[0] > 0:
            X[i[0]] = 1
        else:
            X[abs(i[0])] = 0
    return

# Função para saber se a solução J é completa

def isViable():
    atualizaX()
    # Teste de viabilidade

    s = 0
    for i in range(m):  # Percorrer as restrições
        for j in range(1, n + 1):  # Percorrer variaveis de cada restrição, x1 a x4
            if X[j] == '*':
                continue
            else:
                s += A[i][j] * X[j]
        if s > b[i]:  # se restrição é inviável
            return False
        s = 0
    return True

def prouning(useBalas):
    # Podas por completude ou viabilidade do complemento nulo
    # Se a solução for incompleta e viável, o completamento nulo é o melhor possível
    if len(J) == n or (isViable() and len(J) != n):  
        return True
    if useBalas and goBalas(True, True):
        #debug()
        return True
    return False

# Função de decida da arvore, fixando o elemento mais a direita
def goNext(J):
    bestV = N2[0]
    bestS = math.inf * -1
    for i in N2:
        s = 0
        for j in range(m):
            s = min(0, S[j] - A[j][i])
        if s > bestS:
            bestV = i
            bestS = s

    J.append([bestV, False])
    return J

# Retorna o resultado da função, ou seja, o valor de z para
# os valores atuais de X

def funcObj():
    atualizaX()
    fo = 0
    for i in range(n + 1):
        if X[i] == '*':
            continue
        else:
            fo += X[i] * c[i]

    return fo

# Função para mostrar a viabilidade!

def printViability(J):
    global Zmin, currentZ

    currentZ = funcObj()
    # Só entra se o Z for menor do que o menor já achado, caso
    # contrário não é interessante para nós.
    if currentZ < Zmin:
        if len(J) == n:
            print('J é uma solução completa e viável')
        else:
            print('J é uma solução completa e viável por completamento nulo')
            for i in range(n + 1):
                if X[i] == '*':
                    X[i] = 0
        Zmin = currentZ
        print(f'Funcao objetiva {currentZ} e ', f'X = {X[1:]}')  # Imprimir solução atual viável
        writeInFile(currentZ, X[1:])  # escreve no arquivo a melhor solução
    return


# Função para saber se todos os elementos de J estão sublinhados

def isAllMarked(J):
    condicao = True  # Todos elementos de J são sublinhados
    for i, j in J:
        if not j:
            condicao = False  # PARE, a busca está completa
            break
    return condicao


# In[129]:


while True:
    if not prouning(True):
        J = goNext(J)  # Search for right next free-variable
    else:
        if isViable():
            printViability(J)
        if J[-1][1]:
            if isAllMarked(J):
                break
            else:
                # Função que substitui o elemento não sublinhado, que se encontra mais a direita em J
                # pelo seu complemento sublinhado, e remove todos os elementos a sua direita
                count = 0
                for i, j in J:
                    if not j:
                        count = J.index([i, j])  # Localizar elemento não sublinhado mais a direita
                J[count][0] *= -1
                J[count][1] = not J[count][1]
                del J[count + 1:]  # Change and delete
        else:
            J[-1][0] *= -1
            J[-1][1] = not J[-1][1]  # Substitua o elemento mais a direita em J por seu complemento sublinhado


# In[130]:


print(f'Resultado do Teste de Balas \n   Menor valor de z: {Zmin}')

#file = open('testes\solucao - 25-15.txt', 'r')
#aux = file.readline()
#teachers = int(file.readline())  # numero de variáveis

#print(f'   O resultado do Professor: {teachers}')

#print(f'\nDiferença de {Zmin - teachers} em relação ao do professor!!!')
    

