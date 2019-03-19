/*@

	predicate IndoorLightsInv ( IndoorLights il; ) = 
			il.value |-> ?v
			&*& il.sensorList |-> ?s1
			&*& il.lampsList |-> ?s2
			&*& il.nSensors |-> ?ns
			&*& il.nLamps |-> ?nl
			&*& 0 <= ns &*& ns <= s1.length
			&*& 0 <= nl &*& nl <= s2.length
			&*& array_slice(sensorList,0,ns,?elems)
			&*& array_slice(sensorList,ns,s1.length,?others)
			&*& array_slice(lampsList,0,nl,?elems)
			&*& array_slice(LampsList,nl,s2.length,?others);
@*/

class IndoorLights {
	
	int value;
    	Sensor[] sensorList;
    	Actuator[] lampsList;
    	Log log;
    	
    	int nSensors;
    	int nLamps;

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
               		String output = "value1 = " + presence + " value2 = " + externalLight; 
                	
                	if(presence.get() >  5 && externalLight.get() > 10){
                       	 	for(int i = 0; i < lampsList.length; i++){
                        		lampsList[i].set(true);                        
                        	}
                	}
                	
l			this.log.write("IndoorLights", output, "true");
 	   		TimeUnit.SECONDS.sleep(5);
 		}
    	}   
}
