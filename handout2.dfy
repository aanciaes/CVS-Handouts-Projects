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
  p.setDb(db);
  
  print p.conn.isFull();
  assert p.conn.size >= 0;
  assert !db.isFull();
  
  p.save();
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
    requires conn != null
    requires -1 < id < this.conn.size
    ensures -1 < this.id < this.conn.size
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
    requires db.size >= 0
    requires db.db.Length >= 0
    ensures this.conn != null
    ensures this.conn.size >= 0
    ensures this.conn.db.Length >=0
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
    //requires !this.conn.isFull()
    // if there is a connection and a db is passed, we use the one passed by argument, and must not be full
    //requires this.conn != null && db != null ==> !db.isFull()
    
    requires this.conn.size >= 0
    requires -1 <= this.id < this.conn.size
        
    ensures -1 <= this.id < this.conn.size
    ensures !this.conn.isFull() ==> persistent ()
    ensures this.name.Length > 0
    ensures this.age >= 0
    
  { 
    //var row := new Row ();
    if(!this.conn.isFull()){
      var pos := conn.add (this.id, this.name, this.age); 
      this.setId(pos);
    }
  }
}

class Database {
  
  var db: array<Row?>;
  var size: int;
  
  constructor ()
    ensures fresh (db)
    ensures this.size >= 0
    ensures !this.isFull()
  {
    this.size := 0;
    this.db := new Row? [10];
  }
  
  function method isFull (): bool 
    reads this
  {
    this.size >= this.db.Length
  }
  
  method add (id: int, name: array<char>, age:int) returns (rst: int)
    modifies this`size, this.db
    requires !isFull()
    requires this.size > -1
    requires name.Length > 0
    requires age >= 0
    requires -1 <= id < this.size <= this.db.Length
    ensures this.size > -1
    ensures -1 < rst < this.size
  {
    var pos := id;
    if(id < 0){
         pos:= size;
    }

    db[pos] := new Row();
    db[pos].setName(name);
    db[pos].setAge (age);
    rst := size;
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

