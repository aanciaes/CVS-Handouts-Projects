method Main() 
 
{
  var p: Person := new Person ();

  var name := new char[1];
  name[0] := 'm';
  p.setName(name);
  p.setAge (22);
  
  var db: Database := new Database ();
  print db.size; 
  print "\n";
  
  //p.save();
  print db.size;
}

class Person {
  
  var id:int;
  var name:array<char>; 
  var age:int;
  var conn: Database?;
  
  constructor () 
    ensures transient()
    ensures fresh (name)
  {
    id := -1;
    name := new char[0];
    age := -1;
    conn := null;
  }
  
  function transient () : bool
    reads this
  {
    id == -1
  }
  
  function persistent (): bool
    reads this
  {
    id > -1 && conn !=  null
  }
  
  function detached (): bool
    reads this
  {
    id > -1 && conn ==  null
  }
  
  method setId (id: int) 
    modifies this ` id;
    requires id >= 0
    ensures this.id >= 0
  {
    this.id := id;
  }
  
  method setName (name: array<char>) 
    modifies this ` name;
    requires name.Length > 0
    ensures this.name.Length > 0
  {
    this.name := name;
  }
  
  method setAge (age: int) 
    modifies this ` age;
    requires age >= 0
    ensures this.age >= 0
  {
    this.age := age;
  }
  
  method setDb (db: Database)
    modifies this ` conn
    ensures this.conn != null
  {
    this.conn := db;
  }
  
  method save ()
    modifies this ` id, this.conn.db, this.conn ` size
    requires transient ()
    requires this.name.Length > 0
    requires this.age >= 0
    // if there is no connection, db passed must not be null and must not be full.
    //requires this.conn == null ==> db != null && !db.isFull()
    // if there is a connection and no db is passed, current connection must not be full
    requires this.conn != null
    requires !this.conn.isFull()
    // if there is a connection and a db is passed, we use the one passed by argument, and must not be full
    //requires this.conn != null && db != null ==> !db.isFull()
    
    requires this.conn.size >= 0
    
    ensures persistent ()
    ensures this.name.Length > 0
    ensures this.age >= 0
    
  { 
    //var row := new Row ();
    var pos := conn.add (); 
    this.id := pos;
  }
}

class Database {
  
  var db: array<Row?>;
  var size: int;
  
  constructor ()
    ensures fresh (db)
    ensures this.size >= 0
  {
    this.size := 0;
    this.db := new Row? [10];
  }
  
  function isFull (): bool 
    reads this
  {
    this.size >= this.db.Length
  }
  
  method add () returns (pos: int)
    modifies this`size, this.db
    requires !isFull()
    requires this.size > -1
    ensures this.size > -1
    ensures pos > -1
  {
    db[size] := new Row();
    pos := size;
    size := size + 1;
  }
}

class Row {
  
  var name:array<char>; 
  var age:int;
  
  constructor () 
    ensures fresh (name)
  {
    this.name := new char[0];
    this.age := -1;
  }
  
  method setName (name: array<char>) 
    modifies this ` name
    requires name.Length > 0
    ensures this.name.Length > 0
  {
    this.name := name;
  } 
  
  method setAge (age: int)
    modifies this ` age
    requires age >= 0
    ensures this.age >= 0
  {
    this.age := age;
  }
  
}
