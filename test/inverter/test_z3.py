'''
Created on 04.04.2015

@author: schultschik
'''
import z3

def sel(v1,v2,var):
    s11=z3.Int(var+"11")
    s12=z3.Int(var+"12")
    c=z3.And(s11>=0,s12>0,(s12+s11)==1)
    return c,s12*v1+s12*v2

if __name__ == '__main__':
    x=z3.Int("x")
    y=z3.Int("y")
    v1=z3.Int("v1")
    v2=z3.Int("v2")
    v3=z3.Int("v3")
    p=z3.Int("p")
    q=z3.Int("q")

    c1,s1=sel(x,y,"s1")
    c2,s2=sel(x,y,"s2")

    print c1

    solver=z3.Solver()
    
    solver.add(c1,c2)
    solver.add(z3.ForAll([x,y],z3.And(p==x+y+22,q==2*y)))
    solver.add(z3.ForAll([x,y],z3.And(x==s1*s2+v2,y==p*p+q-v3)))
    
    if solver.check():
        print solver.model()
