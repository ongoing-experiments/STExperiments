package main;

import java.awt.EventQueue;

/**
 * @author jduarte
 * 
 */
public class Main
{
	private static final long serialVersionUID = 4092938070485225093L;
	
	public Main() 
    {

    }
	
	public static void main(String[] args) 
    {
        Main ex = new Main();
        
		EventQueue.invokeLater(new Runnable() 
		{
			public void run() {
				try {
					VLDB msmp = new VLDB(null);
					msmp.setVisible(true);					
				} catch (Exception e) {
					e.printStackTrace();
				}
			}
		});
     }
}