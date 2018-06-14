
class Domotic {
	
	public static void main(String[] args) {
		
        Log log = new Log();
        //RULE ONE   

        Sensor light1 = new Sensor();
        ligth1.start();
        Sensor light2 = new Sensor();
        ligth2.start();

        Sensor[] lightSensors = new Sensor[2];
        lightSensors[0] = light1;
        lightSensors[1] = light2;

		Actuator lamp1 = new Actuator();
        Actuator lamp2 = new Actuator();
        Actuator lamp3 = new Actuator();

        Actuator[] lamps = new Actuator[3];
        lamps[0] = lamp1; 
        lamps[1] = lamp2;
        lamps[2] = lamp3;
             	
		IndoorLights il = new IndoorLights(lightSensors, lamps, log);

        //RULE TWO
        Sensor rain = new Sensor();
        Sensor wind = new Sensor();
        rain.start();
        wind.start();

        Sensor[] rainWindSensors = new Sensor[2];
        rainWindSensors[0] = rain;
        rainWindSensors[1] = wind;

        Actuator window1 = new Actuator();
        Actuator window2 = new Actuator();
        Actuator window3 = new Actuator();

        Actuator[] windows = new Actuator[3];
        windows[0] = window1; 
        windows[1] = window2;
        windows[2] = window3;
		
		RainWindProtection rwp = new RainWindProtection(rainWindSensors, windows, log);

        //START RULES
        il.start();
        rwp.start();
		
		int  last = 0;
		while(true) {
		
			String[] messages = log.read(last);
			last += messages.length;

			//for(String s:messages)
			//filter message by rule/sensor/actuator/room
			//Sys.out(s);	

            TimeUnit.SECONDS.sleep(30);
		}
	}

}
