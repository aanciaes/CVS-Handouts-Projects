import java.util.concurrent.locks.ReentrantLock;

/*@

	predicate SensorInv ( Sensor s; ) = 
			s.value |-> ?v &*& s.max |-> ?max &*& 
			s.min |-> ?min &*& min < max;
@*/

class Sensor {
	
	int value;
	int min;
	int max;

	//ReentrantLock mon;
	
	public Sensor(int min, int max) 
	//@ requires min < max;
	//@ ensures SensorInv(this);
	{
		this.min = min;
		this.max = max;
		this.value = min;
		this.mon = new ReentrantLock();
	}

	
	public int get() 
	//@ requires SensorInv(this);
	//@ ensures SensorInv(this);
	{ return this.value; }

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
