import java.util.concurrent.locks.ReentrantLock;
import java.util.concurrent.locks.Condition;

/*@

	predicate ActuatorInv ( Actuator a; ) = 
			a.value |-> ?v;
@*/

class Actuator {
	int value;

	ReentrantLock mon;
    Condition okRead;
    Condition okWrite;

    boolean ready;
	
	
	public Actuator() 
	//@ requires true;
	//@ ensures ActuatorInv(this);
	{
	this.mon = new ReentrantLock();
    this.okRead = new Condition(mon);
    this.okWrite = new Condition(mon);
    this.read = true;
	}

	
	public int get() 
	//@ requires ActuatorInv(this);
	//@ ensures true; //ActuatorInv(this) &*& result = this.value;
	{ return this.value; }

	public void set(int value) 
	//@ requires ActuatorInv(this);
	//@ ensures ActuatorInv(this);
	{ this.value = value; }

}
