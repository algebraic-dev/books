fib := method(n, if(n < 2, n, (fib(n - 1) + fib (n - 2))))

fib(15) println

fib := method(fibN, 
    n := 1;
    m := 0;
    o := 0;
    for (i, 1, fibN,
        o = n;
        n = n + m;
        m = o;))

fib(15) println