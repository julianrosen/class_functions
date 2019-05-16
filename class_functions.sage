from random import randint
R.<x> = PolynomialRing(QQ)
L = (x^3-2).splitting_field('y')
R = ClassFunctions(QQ)
r = R(7)
r
r.field = L
D = {}
for C in L.galois_group().conjugacy_classes():
    D[C] = randint(-10,10)
r.D = D
r^2
K = (x^2+1).splitting_field('w')
s = R(10)
s.field = K
D = {}
for C in K.galois_group().conjugacy_classes():
    D[C] = randint(-10,10)
s.D = D