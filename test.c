int f( int a, int b, int c, 
       int d, int e, int f, 
       int g, int h, int i) {
    return
      (a+b)*(a-(c-b)) +
        (d+e+f*(d-e/f)+g)*h/i/a/b/c/d ;
}

/*
a = (%ebp+8)
b = (%ebp+12)
c = (%ebp+16)
d = (%ebp+20)
e = (%ebp+24)
f = (%ebp+28)
g = (%ebp+32)
h = (%ebp+36)
i = (%ebp+40)
*/