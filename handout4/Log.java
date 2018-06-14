import java.util.concurrent.*;
import java.util.concurrent.locks.*;

/*@
	predicate_ctor Log_shared_state (Log log)() = 
			log.ready |-> ?r;
			
	predicate_ctor Log_oktoread (Log log) () = 
	log.ready |-> ?okr &*& okr == true;
	
	predicate_ctor Log_oktowrite (Log log) () = 
	log.ready |-> ?okw &*& okw == true;

	predicate LogInv ( Log log; ) = 
			log.mon |-> ?m
			&*& m !=null
			&*& lck(m,1, Log_shared_state(log))
			&*& log.okRead |-> ?okr
			&*& okr != null
			&*& cond(okr, Log_shared_state(log), Log_oktoread(log))
			&*& log.okWrite |-> ?okw
			&*& okw != null
			&*& cond (okw, Log_shared_state(log), Log_oktowrite(log));
@*/


class Log {

String[] messages;
int pos;

boolean ready;
ReentrantLock mon;
Condition okRead;
Condition okWrite;

public Log(){
	this.messages = new String[20];
	this.pos = 0;
	
	this.ready = true;
		
	//@ close Log_shared_state(this)();
	//@ close enter_lck(1,Log_shared_state(this));
	this.mon = new ReentrantLock();
	
	//@ close set_cond(Log_shared_state(this),Log_oktoread(this));
    	this.okRead = mon.newCondition();
    	//@ close set_cond(Log_shared_state(this), Log_oktowrite(this));
    	this.okWrite = mon.newCondition();
    		
    	//@ close LogInv(this);
}

public void write(String rule, String sensors, String act)
	//@ requires [?f]LogInv(this);
	//@ ensures [f]LogInv(this);
	{ 
		//@ open LogInv(this);
      		mon.lock(); 
      		//@ open Log_shared_state(this)();
      		
      		while (!ready)
      		/*@ invariant this.ready |-> ?r
      			&*& [f]this.okRead |-> ?okr
      			&*& okr != null
      			&*& [f]this.okWrite |-> ?okw
      			&*& okw != null
      			&*& [f]cond (okr, Log_shared_state(this), Log_oktoread(this))
      			&*& [f]cond (okw, Log_shared_state(this), Log_oktowrite(this));
      		@*/
      		{
      			//@close Log_shared_state (this)();
      			okWrite.await();
     			//@open Log_oktowrite(this)();	
      
      		}
      		
      		//@assert ready == true;
      		this.ready == false;
		
		String buildFinal = rule + sensors + act;
		messages[pos++] = buildFinal;
		
		this.ready == true;
		//@ close Log_oktowrite(this)();
		this.okWrite.signal();
		
		 mon.unlock(); // release ownership of the shared state
      		//@ close [f]LogInv(this);

}

public String read(int last)
	//@ requires LogInv(this);
	//@ ensures LogInv(this);
{
	String message;
      	//@ open LogInv(this);
      	mon.lock(); 
      	//@ open Log_shared_state(this)();
      	message = this.messages[last]; // put a copy on the stack, private to the thread
      	//@ close Log_shared_state(this)();
      	mon.unlock();	
      	//@ close LogInv(this);
      	return message; 
}

}
