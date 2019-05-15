def compositum(K,L):
    """
    If K and L are number fields, compositum(K,L) is a triple
    (J,f,g), where J is a number field and f:K-->J, g:L-->J
    """
    return K.composite_fields(L,both_maps=True)[0][:-1]

def restrict(C1,f):
    """
    Returns the restriction of the conjugacy class C1 along f
    """
    K,L = f.domain(),f.codomain()
    if not K.is_galois() or not L.is_galois():
        raise ValueError("The domain and codomain of f must be Galois over Q")
    x = K.gens()[0]
    G,H = K.galois_group(),L.galois_group()
    for C2 in G.conjugacy_classes():
        g = C2.an_element()
        for h in C1:
            if g(f(x)) == f(h(x)):
                return C2
    # This should not happen
    raise Exception("Could not restrict")

Number = (Integer,Rational)

class ClassFunctions(Ring):
    # Element = ArtPerElement
    def __init__(self,base=QQ):
        Ring.__init__(self,base=QQ)
        self._populate_coercion_lists_()
        
    def _repr_(self):
        return "The ring of locally constant class functions on the absolute Galois group of Q, with values in "+str(self.base)
    
    def _latex_(self):
        return r"\text{The ring of locally constant class functions on }\operatorname{Gal}(\bar{\mathbb{Q}}/\mathbb{Q})\text{, with values in }"+latex(self.base)
    
    def _element_constructor_(self,s):
        return ClassFunction(self,s)
    
    def _coerce_map_from_(self,S):
        if self.base().coerce_map_from(S):
            return True
        elif isinstance(S,ClassFunctions) and self:
            return True
        print "Coercion failed: ",S,parent(S)
        return False
    

class ClassFunction(RingElement):
    """
    Objects of this class are locally constan class functions on
    the absolute Galois group of Q
    """
    def __init__(self,parent,s):
        RingElement.__init__(self,parent)
        if isinstance(s,Number):
            try:
                self.field = PolynomialRing(QQ,'x').one().splitting_field('x')
            except:
                print "Field failed"
            self.gen = self.field.gens()[0]
            self.D = {self.group().an_element():parent.base()(s)}
            self.desc = str(s)
        elif isinstance(s,ClassFunction):
            self.field = s.field
            self.gen = s.gen
            self.D = dict(s.D)
            self.desc = str(s.desc)
            self.clean()
        elif isinstance(s,dict):
            self.field = s.keys()[0].as_hom().domain()
            self.gen = self.field.gens()[0]
            self.D = dict(s)
            self.desc = str(s)
            self.clean()
        else:
            raise ValueError('Cannot construct class function from type '+str(type(s)))
    
    def group(self):
        return self.field.galois_group()
    
    def _repr_(self):
        return self.disp(string=True)
        return 'A class function'
    
    def clean(self):
        S = self.field.subfields()
        S = [(s[0],s[1]) for s in S]
        S.sort(key=lambda s:s[0].degree())
        for L,f in S:
            for C in self.D:
                try:
                    L(self.D[C])
                except:
                    break
            else:
                D = {}
                for C in self.D:
                    rho = restrict(C,f)
                    r = L(self.D[C])
                    if rho in D and D[rho] != r:
                        break
                    else:
                        D[rho] = r
                else:
                    self.D = D
                    self.field = L
                    return self
        return self
       
    
    def extend_field(self,f):
        K,L = f.domain(),f.codomain()
        assert self.field is K
        assert L.is_galois()
        D = {}
        for C in L.galois_group().conjugacy_classes():
            rho = restrict(C,f)
            assert rho in K.galois_group().conjugacy_classes()
            if rho not in self.D:
                print self.field
                print rho
                print self.D
                raise Exception("Error")
            D[h] = f(self.D[restrict(h,f)])
        T = ClassFunction(parent(self),0)
        T.D = D
        T.field = L
        return T
    
    def _add_(self, s):
        T = s
        J,f,g = compositum(self.field,T.field)
        selfE,TE = self.extend_field(f),T.extend_field(g)
        assert selfE.field is J and TE.field is J
        for x in TE.D:
            TE.D[x] += selfE.D[x]
        return TE
    
    def __eq__(self,other):
        if isinstance(other,ClassFunction):
            s = other
        elif parent(self).coerce_map_from(parent(other)):
            s = parent(self)(other)
        else:
            raise ValueError("Connot compare elements")
        J,f,g = compositum(self.field,s.field)
        D1,D2 = self.extend_field(f).D,s.extend_field(g).D
        for x in D1:
            assert x in D2
            assert parent(D1[x]) is parent(D2[x])
            if D1[x] != D2[x]:
                return (D1,D2)
                return False
        return True
    
    def _mul_(self, s):
        T = s
        #T = ArtPer(s)
        J,f,g = compositum(self.field,T.field)
        selfE,TE = self.extend_field(f),T.extend_field(g)
        assert selfE.field is J and TE.field is J
        for x in TE.D:
            TE.D[x] *= selfE.D[x]
        return TE
    
    def _sub_(self,s):
        return self + (-1)*s
    def _pow_(self,n):
        if n == 0:
            return ClassFunction(1)
        elif n > 0:
            return self*self**(n-1)
        elif n < 0:
            return (self^(-n)).inv()
    
    def disp(self,string=False):
        S = ""
        S = S + "\tClass function on the Galois group of "+str(self.field)+"\n"
        for C in self.D:
            S = S + "\t" + str(C) + " maps to " + str(self.D[C]) + "\n"
        S = S[:-1]
        if string:
            return S
        else:
            print S
            return None
    

    
    def inv(self):
        if not self.is_inv():
            raise ValueError("Element is not invertible")
        T = ArtPerElement(self.parent(),self)
        for x in T.D:
            T.D[x] = T.D[x]^(-1)
        return T
    
    def is_inv(self):
        for x in self.D:
            if self.D[x] == 0:
                return False
        return True
    
    def _div_(self, s):
        if isinstance(s,Number):
            return self*(self.base()(1)/s)
        else:
            return self * s.inv()
        
    def minimal_polynomial(self):
        L = [self.D[x].minpoly() for x in self.D]
        return lcm(L)