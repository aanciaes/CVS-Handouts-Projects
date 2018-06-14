import java.util.concurrent.*;
import java.util.concurrent.locks.*;

/*@
	predicate_ctor Actuator_shared_state (Actuator a) () =
	a.value |-> ?v &*& a.ready |-> ?r;
	
	predicate_ctor Actuator_oktoread (Actuator a) () = 
	a.value |-> ?v &*& a.ready |-> ?okr &*& okr == true;
	
	predicate_ctor Actuator_oktowrite (Actuator a) () = 
	a.value |-> ?v &*& a.ready |-> ?okr &*& okr == true;

	predicate ActuatorInv ( Actuator a; ) = 
			a.mon |-> ?m
			&*& m !=null
			&*& lck(m,1, Actuator_shared_state(a))
			&*& a.okRead |-> ?okr
			&*& okr != null
			&*& cond(okr, Actuator_shared_state(a), Actuator_oktoread(a))
			&*& a.okWrite |-> ?okw
			&*& okw != null
			&*& cond (okw, Actuator_shared_state(a), Actuator_oktowrite(a));
			
@*/

class Actuator {

	
	ReentrantLock mon;
    	Condition okRead;
    	Condition okWrite;

	int value;
    	boolean ready;
	
	
	public Actuator() 
	//@ requires true;
	//@ ensures ActuatorInv(this);
	{
		this.value=0;
		this.ready == true;
		//@ close Actuator_shared_state(this)();
		//@ close enter_lck(1,Actuator_shared_state(this));
		this.mon = new ReentrantLock();
		
		//@ close set_cond(Actuator_shared_state(this),Actuator_oktoread(this));
    		this.okRead = mon.newCondition();
    		//@ close set_cond(Actuator_shared_state(this), Actuator_oktowrite(this));
    		this.okWrite = mon.newCondition();
    		
    		//@ close ActuatorInv(this);
	}

	
	public int get() 
	//@ requires ActuatorInv(this);
	//@ ensures ActuatorInv(this);
	{
		int v;
      		//@ open ActuatorInv(this);
      		mon.lock(); 
      		//@ open Actuator_shared_state(this)();
      		v = value; // put a copy on the stack, private to the thread
      		//@ close Actuator_shared_state(this)();
      		mon.unlock();	
      		//@ close ActuatorInv(this);
      		
      		return v;
	}

	public void set(int value) 
	//@ requires [?f]ActuatorInv(this);
	//@ ensures [f]ActuatorInv(this);
	{ 
		//@ open ActuatorInv(this);
      		mon.lock(); 
      		//@ open Actuator_shared_state(this)();
      		
      		while (!ready)
      		/*@ invariant this.value |-> ?v
      			&*& this.ready |-> ?r
      			&*& [f]this.okRead |-> ?okr
      			&*& okr != null
      			&*& [f]this.okWrite |-> ?okw
      			&*& okw != null
      			&*& [f]cond (okr, Actuator_shared_state(this), Actuator_oktoread(this))
      			&*& [f]cond (okw, Actuator_shared_state(this), Actuator_oktowrite(this));
      		@*/
      		{
      			//@close Actuator_shared_state (this)();
      			okWrite.await();
     			//@open Actuator_oktowrite(this)();	
      
      		}
      		
      		//@assert ready == true;
      		this.ready == false;
		this.value = value; 
		
		this.ready == true;
		//@ close Actuator_oktowrite(this)();
		this.okWrite.signal();
		
		
		
		 mon.unlock(); // release ownership of the shared state
      		//@ close [f]ActuatorInv(this);
	}

}
