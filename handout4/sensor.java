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

	predicate SensorInv ( Sensor s; ) = 
			s.mon |-> ?m
			&*& m !=null
			&*& lck(m,1, Sensor_shared_state(s));
@*/

class Sensor {
	
	int value;
	int min;
	int max;

	ReentrantLock mon;
	
	public Sensor(int min, int max) 
	//@ requires min < max;
	//@ ensures SensorInv(this);
	{
		this.min = min;
		this.max = max;
		this.value = min;
		
		//@ close Sensor_shared_state(this)();
		//@ close enter_lck(1,Sensor_shared_state(this));
		this.mon = new ReentrantLock();
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
	//@ requires SensorInv(this);
	//@ ensures SensorInv(this);
	{ this.value = value; }


	private void start()
		/*@ requires [_]System_out(?o) &*& o != null
		
		&*& SensorInv(_);
		@*/
		//@ ensures true;
	{

		while(true) 
		/*@ invariant [_]System_out(o) &*& o != null
		&*& [_]TimeUnit_SECONDS(ss) &*& ss != null
		&*& SensorInv(s, 10, 0);
		@*/		
		{
			TimeUnit.SECONDS.sleep(5);
			
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
		}
	}
}
