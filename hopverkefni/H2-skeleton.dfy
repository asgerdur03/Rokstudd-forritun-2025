// Author of question: Snorri Agnarsson
// Permalink of question: https://tinyurl.com/3xz4kd2p

// Authors of solution:   Ásgerður og Vilborg
// Permalink of solution: https://tinyurl.com/58mf24vz

// Use the command
//   dafny build H2-skeleton.dfy
// to compile the file.
// Or use the web page tio.run/#dafny.

// When you have solved the problem put
// the solution on the Dafny web page,
// generate a permalink and put it in
// this file or email the solution to me.

method SearchRecursive( a: seq<real>, i: int, j: int, x: real ) returns ( k: int ) 
    decreases j-i
    requires 0 <= i <= j <= |a| // i og j eru innan range
    requires forall p,q | i <= p < q < j :: a[p] >= a[q] // allt fylki er decreasing
    ensures i <= k <= j
    ensures forall u | i <= u < k :: a[u] >= x // krafa frá test case
    ensures forall u | k <= u < j :: a[u] < x

{
    if i == j
    {
        k := i;
        return k;
    }
    var m := i+(j-i)/2;
    if a[m] < x
    {
        k := SearchRecursive(a,i,m,x);
    }
    else
    {
        k := SearchRecursive(a,m+1,j,x);
    }

}


method SearchLoop( a: seq<real>, i: int, j: int, x: real ) returns ( k: int )
    requires 0 <= i <= j <= |a| // in raange
    requires forall p,q | i <= p < q < j :: a[p] >= a[q] // decending röð
    ensures i <= k <= j
    ensures forall u | i <= u < k :: a[u] >= x // krafa frá test case
    ensures forall u | k <= u < j :: a[u] < x
{
    var p := i;
    var q := j;
    while p != q
        decreases q-p
        invariant i <= p <= q <= j
        
        invariant forall u | i <= u < p :: a[u] >= x
        invariant forall u | q <= u < j :: a[u] < x
        

    {
        var m := p+(q-p)/2;
        if a[m] >= x
        {
            p := m+1;
        }
        else
        {
            q := m;
        }
    }
    return p;
}



// Ef eftirfarandi fall er ekki samþykkt þá eru
// föllin ekki að haga sér rétt að mati Dafny.

// If the following method is not accepted then
// the functions are not behaving correctly in
// Dafny's opinion.

method Test( a: seq<real>, x: real )
    requires forall p,q | 0 <= p < q < |a| :: a[p] >= a[q] // a er sorted, öfurt (decending)
{
    
    var k1 := SearchLoop(a,0,|a|,x);
    assert forall r | 0 <= r < k1 :: a[r] >= x;
    assert forall r | k1 <= r < |a| :: a[r] < x;


    var k2 := SearchRecursive(a,0,|a|,x);
    assert forall r | 0 <= r < k2 :: a[r] >= x; // allt "framar" en k2 er >= x
    assert forall r | k2 <= r < |a| :: a[r] < x; // allt "eftir" k2 er < x 

    // a[i...k-1] >= x > a[k...j-1]
}