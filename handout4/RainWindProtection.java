/*@

	predicate IndoorLightsInv ( IndoorLights il; ) = 
			il.value |-> ?v
			&*& il.sensorList |-> ?s1
			&*& il.windowsList |-> ?w2
			&*& il.nSensors |-> ?ns
			&*& il.nWindows |-> ?nw
			&*& 0 <= ns &*& ns <= s1.length
			&*& 0 <= nw &*& nw <= w2.length
			&*& array_slice(sensorList,0,ns,?elems)
			&*& array_slice(sensorList,ns,s1.length,?others)
			&*& array_slice(windowsList,0,nw,?elems)
			&*& array_slice(windowsList,nw,w2.length,?others);
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
            
            		
                	Sensor rain = sensorList.get(0);
                	Sensor wind = sensorList.get(1);
                
                	int val1 = rain.get();
                	int val2 = wind.get();
                	
                	String output = "value1 = " + val1 + " value2 = " + val2; 
	
                	if(val1 >  5 && val2 > 10){
                        
                        	for(int i = 0; i < windowsList.length; i++){
                        		windowsList[i].set(true);                        
                        	}

                        	log.write("Rain/WindProtection", output, "true");
                        	TimeUnit.SECONDS.sleep(5);
                	}
    		}   
    	}	
}
