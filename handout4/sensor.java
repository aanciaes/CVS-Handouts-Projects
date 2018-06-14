import java.util.concurrent.*;
import java.util.concurrent.locks.*;
import java.util.*;

/*@
	predicate_ctor Sensor_shared_state (Sensor s)() =
			s.value |-> ?v 
			&*& s.max |-> ?max 
			&*& s.min |-> ?min 
			&*& min < max 
			&*& v>=min
			&*& v<=max
			&*& s.ready |-> ?r;
			
	predicate_ctor Sensor_oktoread (Sensor s) () = 
			s.value |-> ?v 
			&*& s.ready |-> ?okr 
			&*& okr == true
			&*& s.max |-> ?max 
			&*& s.min |-> ?min 
			&*& min < max 
			&*& v>=min
			&*& v<=max;
	
	predicate_ctor Sensor_oktowrite (Sensor s) () = 
			s.value |-> ?v 
			&*& s.ready |-> ?okr 
			&*& okr == true
			&*& s.max |-> ?max 
			&*& s.min |-> ?min 
			&*& min < max 
			&*& v>=min
			&*& v<=max;

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
	
	public Sensor(int MIN, int MAX) 
	//@ requires MIN < MAX;
	//@ ensures SensorInv(this);
	{
		this.min = MIN;
		this.max = MAX;
		this.value = MIN;
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
      			&*& this.min |-> ?min
      			&*& this.max |-> ?max
      			&*& min < max
      			&*& v >= min
      			&*& v<=max
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
      		if(value > max){
			this.value = this.max;
		}else if(value < min){
			this.value = this.min;
		} else this.value=value; 
		
		this.ready == true;
		//@ close Sensor_oktowrite(this)();
		this.okWrite.signal();
		
		 mon.unlock(); // release ownership of the shared state
      		//@ close [f]SensorInv(this);
	}


	private void start()
		/*@ requires [_]System_out(?o) &*& o != null
			     &*& [?f]SensorInv(this);
		@*/
		//@ ensures true;
	{
		//@open SensorInv(this);
		
		while(true) 
		//@invariant true;
		{
			//gerar random
			Random r = new Random();
			int random = r.nextInt(100000);
			
			set(random);
		
			TimeUnit.SECONDS.sleep(5);
								
		}
	}
}
