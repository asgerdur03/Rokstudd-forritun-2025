// Author of question: Snorri Agnarsson
// Permalink of question: https://tinyurl.com/mssdpfvr

// Author of solution:    Ásgerður Júlía Gunnarsdóttir og Vilborg Erlendsdóttir
// Permalink of solution: https://tinyurl.com/5n86s2yj


method SearchRecursive( a: seq<int>, i: int, j: int, x: int ) returns (k: int)
    requires 0 <= i <= j <= |a| // i og j þurfa að vera á milli 0 og lengdar a, og i getur ekki verið hærri en j
    ensures i <= k < j || k == -1  // k skilar gildi, eða -1 ef það er ekki í runu
    ensures k != -1 ==> a[k] == x // k skilar ekki -1 ef stak er til staðar
    ensures k != -1 ==> forall r | k < r < j :: a[r] != x 
    ensures k == -1 ==> forall r | i <= r < j :: a[r] != x
    decreases j-i // bætt við
{
    // hér kemur recursive
    if  i == j{
        k := -1;
        return;
    }
    
    if a[j-1] == x{ // því a[j] er out of bounds
        k := j-1;
        return;
    }
    else{
        k := SearchRecursive(a,i,j-1,x); // lækka j þar til j==i eða tala finnst
    }
}

method SearchLoop( a: seq<int>, i: int, j: int, x: int ) returns (k: int)
    // blabla sömu conditions og í SearchRecursive
    requires 0 <= i <= j <= |a|
    ensures i <= k < j || k == -1
    ensures k != -1 ==> a[k] == x
    ensures k != -1 ==> forall r | k < r < j :: a[r] != x
    ensures k == -1 ==> forall r | i <= r < j :: a[r] != x
{
    // hér kemur loop
    var loopari := j;

    if i == j 
    { 
        k := -1;
        return;
    }

    while loopari > i 
        decreases loopari
        invariant forall p | loopari<= p < j :: a[p] != x

        {
            if a[loopari-1] == x{ return loopari-1;}
            loopari := loopari-1;
        }
    k := -1;
}

method Main() {
    var a := [1, 5, 3, 4, 5, 3];
    var x := 5;
    
    
    print "Loop Search:\n";
    var k2 := SearchLoop(a, 1, 3, x);
    print "Result: ";
    print k2;
    print "\n";

    print "recursive Search:\n";
    var k1 := SearchRecursive(a, 1, 3, x);
    print "Result: ";
    print k1;
    print "\n";
}
