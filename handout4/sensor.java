import java.util.concurrent.*;
import java.util.concurrent.locks.*;

/*@
	predicate_ctor Sensor_shared_state (Sensor s)() =
			s.value |-> ?v 
			&*& s.max |-> ?max 
			&*& s.min |-> ?min 
			&*& min < max 
			&*& v>=min 
			&*& v<=max;
			
	predicate_ctor Sensor_oktoread (Sensor s) () = 
	s.value |-> ?v &*& s.ready |-> ?okr &*& okr == true;
	
	predicate_ctor Sensor_oktowrite (Sensor s) () = 
	s.value |-> ?v &*& s.ready |-> ?okr &*& okr == true;

	predicate SensorInv ( Sensor s; ) = 
			s.mon |-> ?m
			&*& m !=null
			&*& lck(m,1, Sensor_shared_state(s))
			&*& s.okRead |-> ?okr
			&*& okr != null
			&*& cond(okr, Sensor_shared_state(s), Sensor_oktoread(s))
			&*& s.okWrite |-> ?okw
			&*& okw != null
			&*& cond (okw, Sensor_shared_state(s), Sensor_oktowrite(s));
@*/

class Sensor {
	
	int value;
	int min;
	int max;
	
	boolean ready;
	ReentrantLock mon;
	Condition okRead;
    	Condition okWrite;
	
	public Sensor(int min, int max) 
	//@ requires min < max;
	//@ ensures SensorInv(this);
	{
		this.min = min;
		this.max = max;
		this.value = min;
		this.ready = true;
		
		//@ close Sensor_shared_state(this)();
		//@ close enter_lck(1,Sensor_shared_state(this));
		this.mon = new ReentrantLock();
		
		//@ close set_cond(Sensor_shared_state(this),Sensor_oktoread(this));
    		this.okRead = mon.newCondition();
    		//@ close set_cond(Sensor_shared_state(this), Sensor_oktowrite(this));
    		this.okWrite = mon.newCondition();
    		
    		//@ close SensorInv(this);
	}

	
	public int get() 
	//@ requires SensorInv(this);
	//@ ensures SensorInv(this);
	{ 
		int v;
      		//@ open SensorInv(this);
      		mon.lock(); 
      		//@ open Sensor_shared_state(this)();
      		v = this.value; // put a copy on the stack, private to the thread
      		//@ close Sensor_shared_state(this)();
      		mon.unlock();	
      		//@ close SensorInv(this);
      		return v;
	}

	public void set(int value) 
	//@ requires [?f]SensorInv(this);
	//@ ensures [f]SensorInv(this);
	{ 
		//@ open SensorInv(this);
      		mon.lock(); 
      		//@ open Sensor_shared_state(this)();
      		
      		while (!ready)
      		/*@ invariant this.value |-> ?v
      			&*& this.ready |-> ?r
      			&*& [f]this.okRead |-> ?okr
      			&*& okr != null
      			&*& [f]this.okWrite |-> ?okw
      			&*& okw != null
      			&*& [f]cond (okr, Sensor_shared_state(this), Sensor_oktoread(this))
      			&*& [f]cond (okw, Sensor_shared_state(this), Sensor_oktowrite(this));
      		@*/
      		{
      			//@close Sensor_shared_state (this)();
      			okWrite.await();
     			//@open Sensor_oktowrite(this)();	
      
      		}
      		
      		//@assert ready == true;
      		this.ready == false;
		this.value = value; 
		
		this.ready == true;
		//@ close Sensor_oktowrite(this)();
		this.okWrite.signal();
		
		 mon.unlock(); // release ownership of the shared state
      		//@ close [f]SensorInv(this);
	}


	private void start()
		/*@ requires [_]System_out(?o) &*& o != null
			     &*& SensorInv(_);
		@*/
		//@ ensures true;
	{

		while(true) 
		/*@ invariant SensorInv(this);
      		@*/
		{
		
			//@ open SensorInv(this);
			this.mon.lock();
			
			int tmp = this.get();
			
			//@ close SensorInv(this);
			this.mon.unlock();
			
			if(tmp < this.min)
				System.out.println("Got value: " + Integer.toString(this.min));
			else if(tmp > this.max)
				System.out.println("Got value: " + Integer.toString(this.max));
			else
				System.out.println("Got value : " + Integer.toString(tmp));
				
			TimeUnit.SECONDS.sleep(5);
								
		}
	}
}
