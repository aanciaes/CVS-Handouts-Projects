/*@

	predicate RainWindProtectionInv ( Actuator a; ) = 
			a.value |-> ?v;
@*/

class RainWindProtection {
	
	int value;
    
    	Sensor[] sensorList;
    	Actuator[] windowsList;
    	Log log;

	public RainWindProtection(Sensor[] sList, Actuator[] windows, Log log) 
	//@ requires true;
	//@ ensures true;
	{
        	this.sensorList = sList;
		this.windowsList = windows; 
       		this.log = log;
	}

	public void start(){
        
        	while(true){
            
            		TimeUnit.SECONDS.sleep(5);
                	Sensor rain = sensorList.get(0);
                	Sensor wind = sensorList.get(1);
                
                	int val1 = rain.get();
                	int val2 = wind.get();
                	
                	String output = "value1 = " + val1 + " value2 = " + val2; 
	
                	if(val1 >  5 && val2 > 10){
                        
                        	//for(Actuator a : windowsList){
                        	a.set(1);                        
                        	//}

                        	log.write("Rain/WindProtection", output, "true");
                	}
    		}   
    	}	
}
