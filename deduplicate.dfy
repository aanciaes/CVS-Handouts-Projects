//Miguel Anciães
//43367

/**
//Tests were provoking an error where the online dafny compiler would not evaluate the rest. With them commented, no errors found
method Main () {
  
  //Some tests
  
  var input := new int [0];
  var n := input.Length;
  var b, m := Deduplicate (input, n);
  
  assert b.Length == 0;
  assert m == 0;
  assert forall k :: 0 <= k < n ==> contains (b, m, input[k]);
  assert forall k :: 0 <= k < m ==> contains (input, n, b[k]);
  
  input := new int [5];
  input [0] := 1; input [1] := 2; input [2] := 3; input [3] := 4; input [4] := 5;
  n := input.Length;
  b, m := Deduplicate (input, n);
  
  assert m == 5;
  assert forall k :: 0 <= k < n ==> contains (b, m, input[k]);
  assert forall k :: 0 <= k < m ==> contains (input, n, b[k]);
  
  input := new int [5];
  input [0] := 1; input [1] := 1; input [2] := 3; input [3] := 4; input [4] := 4;
  n := input.Length;
  b, m := Deduplicate (input, n);
  
  assert m == 3;
  assert forall k :: 0 <= k < n ==> contains (b, m, input[k]);
  assert forall k :: 0 <= k < m ==> contains (input, n, b[k]);
  
  var i := 0;
  while i<m {
    print (b[i]);
    print ("\n");
    i := i+1;
  }
}
*/

method Deduplicate(a:array<int>, n:int) returns (b:array<int>, m:int)
  requires a.Length >= 0
  requires 0 <= n <= a.Length
  requires sorted(a,n)
  ensures b.Length >= 0
  ensures 0 <= m <= b.Length
  ensures b.Length <= a.Length
  ensures 0 <= m <= n
  ensures sorted(b,m) && unique(b,0,m)
  ensures forall k :: 0 <= k < m ==> contains (a, n, b[k])
  ensures forall k :: 0 <= k < n ==> contains (b, m, a[k])
{
  
  m := 0;
  b := new int[n];
  var i:= 0;
 
  while i<n
    decreases n-i
    invariant 0 <= m <= i <= n
    invariant 0 <= m <= b.Length
    //invariant sorted (b, m) && unique (b, 0, m)
    invariant forall k :: 0 <= k < m ==> contains (a, n, b[k])
    invariant forall k :: 0 <= k < i ==> contains (b, m, a[k])
    
    invariant forall j :: 0 <= j < m && i < n ==> b[j] < a[i]
    invariant forall j,k :: (0 <= j < k < m) ==> b[j] < b[k]
  {
    
   var value:= a[i];
   b[m] := value;
   
   //assert a[i] == b[m];
   assert forall k :: 0 <= k < i ==> contains (b, m, a[k]);
   i:= i+1;
   m:= m+1;
  
   var initGroup := i-1;
   while i<n && a[i] == value
     decreases n-i
     invariant i <= n <= a.Length
     invariant 0 <= initGroup <= i
     invariant forall j :: initGroup <= j < i ==> a[j] == value
   {
       i:= i+1;  
    }
  }
}

function sorted(a:array<int>, n:int):bool
    requires 0 <= n <= a.Length
    reads a
{ 
    forall i, j:: (0 <= i < j < n) ==> a[i] <= a[j] 
}

function unique(b:array<int>, l:int, h:int):bool
    reads b;
    requires 0 <= l <= h <= b.Length
{ 
     forall k::(l<=k<h) ==> forall j::(k<j<h) ==> b[k] != b[j] 
}

function contains(b:array<int>, m:int, v:int):bool
    requires 0 <= m <= b.Length 
    reads b
{
    // exists l :: 0 <= l < m && b[l] == v
    v in b[..m]
}