class Secret{
  var secret : int; // A secret number between 1...10
  var known : bool; // Has the secret been guessed yet?
  var count : int;  // How many guesses has been made?
  
  method Init(x: int)
    requires 0 < x <= 10
    ensures secret == x
    ensures count == 0
    ensures !known
    modifies this
  {
    known := false;
    count := 0;
    secret := x;
  }
  
  method Guess(g : int) returns (result : bool, guesses : int)
    requires !known
    ensures count == old(count) + 1
    ensures g == secret <==> known
    ensures result <==> known
    ensures guesses == count
    modifies `count, `known
  {
    count := count + 1;
    if (g == secret) {
      known := true;
    }
    result := known;
    guesses := count;
  }
  
  method Main(){
    var s := new Secret;
    s.Init(7);
    assert (!s.known);
    assert (s.count == 0);

    var r, g := s.Guess(3);
    assert (!r);
    assert (g == 1);

    r, g := s.Guess(7);
    assert (r);
    assert (g == 2);
  }
}
