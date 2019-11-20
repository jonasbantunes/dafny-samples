// using a datatype for types with a finite number of values is
// simpler than using integer with complex invariants
datatype Value = Empty | X | O

class Tictactoe {
  // game board
  var board : array<Value> ;

  predicate valid()
    reads this
  {
    board != null && board.Length == 9
  }
  
  constructor Init()
    ensures valid()
    ensures forall i :: 0 <= i < 9 ==> board[i] == Empty
    ensures fresh(board)
    modifies this
  {
    board := new Value[9];
    forall (i | 0 <= i < 9 ) {
      board[i] := Empty;       
    }
  }

  // by using the keyword "function method", we can use this function
  // in specifications as well as in imperative code
  function method BoardPosition (x:int, y:int) : int
    requires 0 <= x < 3 && 0 <= y < 3
    ensures 0 <= BoardPosition(x,y) < 9
  {
    y * 3 + x
  }
  
  method PutValue(x:int, y:int, val:Value)
    requires valid()
    requires 0 <= x < 3 && 0 <= y < 3
    requires val == X || val == O
    requires board[BoardPosition(x,y)] == Empty
    ensures valid()
    ensures board[BoardPosition(x,y)] == val
    ensures forall i :: 0 <= i < 9 && i != BoardPosition(x, y) ==> board[i] == old(board[i])
    modifies board
  {
    board[BoardPosition(x,y)] := val ;
  }

  method Main () 
  {
     var game := new Tictactoe.Init();     
     assert (game.board[0] == Empty);     
   
     var aux : int ;
     aux := game.BoardPosition(1,1) ;
     assert aux == 4 ;
     
     game.PutValue(1,1,X) ;               
     assert game.board[4] == X;
      
     aux := game.BoardPosition(2,1) ;
     assert aux == 5 ;     
     
     game.PutValue(2,1,O) ;
     assert game.board[5] == O;     
  }
}
