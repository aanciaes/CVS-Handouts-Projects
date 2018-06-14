/*@

	predicate IndoorLightsInv ( Actuator a; ) = 
			a.value |-> ?v;
@*/

class IndoorLights {
	
	int value;
    
    	Sensor[] sensorList;
    	Actuator[] lampsList;
    	Log log;

	public IndoorLights(Sensor[] sList, Actuator[] lamps, Log log) 
	//@ requires true;
	//@ ensures true;
	{
        	this.sensorList = sList;
	    	this.lampsList = lamps;
       		this.log = log;
	}

	public void start(){
        
        	while(true){
            
                	Sensor presence = sensorList[0];
                	Sensor externalLight = sensorList[1];
               
                	if(presence.get() >  5 && externalLight.get() > 10){
                       	 	//for(Actuator a : lampsList){
                        	    //a.set(1);                        
                        	//}
                	}

 	   		TimeUnit.SECONDS.sleep(5);
 		}
    	}   
}
