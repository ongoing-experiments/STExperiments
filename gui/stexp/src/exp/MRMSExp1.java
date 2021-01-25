package exp;

import java.awt.BasicStroke;
import java.awt.BorderLayout;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.RenderingHints;
import javax.swing.JFrame;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.border.EmptyBorder;
import javax.swing.border.LineBorder;
import javax.swing.event.ChangeEvent;

import org.geotools.geometry.jts.JTSFactoryFinder;
import org.geotools.geometry.jts.LiteShape;
import org.locationtech.jts.geom.Coordinate;
import org.locationtech.jts.geom.Geometry;
import org.locationtech.jts.geom.GeometryFactory;
import org.locationtech.jts.geom.LineString;
import org.locationtech.jts.geom.MultiPolygon;
import org.locationtech.jts.geom.Point;
import org.locationtech.jts.geom.Polygon;
import org.locationtech.jts.io.ParseException;
import org.locationtech.jts.io.WKTReader;
import org.locationtech.jts.util.GeometricShapeFactory;

import structures.Data;
import tools.ScreenImage;

import javax.swing.JButton;
import java.awt.event.ActionListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.event.MouseWheelEvent;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.awt.geom.AffineTransform;
import java.awt.image.BufferedImage;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Timer;
import java.util.TimerTask;
import java.awt.event.ActionEvent;
import javax.swing.JTextField;
import java.awt.Color;
import javax.swing.JSlider;

import javax.swing.event.ChangeListener;
import javax.swing.text.SimpleAttributeSet;
import javax.swing.text.StyleConstants;
import javax.swing.text.StyledDocument;
import javax.swing.JLabel;
import javax.swing.JCheckBox;
import java.awt.Font;
import javax.swing.JTextArea;
import javax.swing.JComboBox;
import javax.swing.DefaultComboBoxModel;
import java.awt.SystemColor;
import javax.swing.JTextPane;

public class MRMSExp1 extends JFrame 
{
	private static final long serialVersionUID = 6237268416941231840L;
	
	private JPanel contentPane;
	
	private JTextField save_picture_to_tx;

	private JButton save_to_picture_bt;
	
	private JButton show_m_region_evolution_bt;
	
	private JSlider show_m_region_evolution_slider;
	
	private JPanel viz_p;
	
	private JFrame f;
	
	private JPanel jp;
	
	private JLabel status;
	
	private JPanel tools_p;
	
	private JButton zoom_out_bt;
	
	private JButton zoom_in_bt;
	
	private JButton show_footprint_bt;
	
	private JLabel zoom_level;
	
	public static final double DEFAULT_ZOOM_MULTIPLICATION_FACTOR = 0.25;
	public static final double DEFAULT_MIN_ZOOM_LEVEL = 0.25;
	public static final double DEFAULT_MAX_ZOOM_LEVEL = 100;
	
    private double zoomLevel = 1.0;
    private double minZoomLevel = DEFAULT_MIN_ZOOM_LEVEL;
    private double maxZoomLevel = DEFAULT_MAX_ZOOM_LEVEL;
    private double zoomMultiplicationFactor = DEFAULT_ZOOM_MULTIPLICATION_FACTOR;
    
    private JTextField rate;
    
    private int geom_to_show_id = 0;
    
    private GeometryFactory geometryFactory;
    private WKTReader reader;
    
    private int Nr;
    
    private String[] mr_p_i;
    private int mr_p_i_len;
    
    private int max;
    
    private TimerTask play_task;
    
	private int w_center;
	private int h_center;
    
	private double cx = 0;
	private double cy = 0;

    private Timer timer;
    private JTextField step;
    private JCheckBox fill;

    private JSlider zoom;
    
    private JLabel n_samples;
    
    private JTextField n_samples_tx;
    private JButton reset_bt;
    private JTextField i_e_tx;
    private Geometry geometry;
    private JTextField i_b_tx;
    private JButton mr_p_i_bt;
    private String intersection_info;
    private String solver_execution_time;
    private JCheckBox print_solver_execution_time_cb;
    private JTextField p_radius_tx;
    private JTextArea mr_p_tx;
    private JTextArea mp1_data_tx;
    private JCheckBox pass_through_control_points_cb;
    private JCheckBox print_intersection_information_cb;
    
    private String[] titles;
    private String[] mss_data;
    private String[] mps_data;
    private String[] intervals;
    private String[] tests_description;
	private JTextPane test_desc_tp;
	private JTextField s_precision_tx;
	private JTextField n_dec_dig_tx;
	private JComboBox<String> op_cb;
	private String operation;
	private JTextArea mr_q_tx;
	private String intersection_geom;
	private JButton save_all_to_png_bt;
	private JTextField gran_tx;
	private JTextArea mp2_data_tx;
    
	public MRMSExp1(Data d) 
	{	
		mr_p_i = null;
		Nr = 0;
		f = this;
		
		//boolean load_tests_information = true;
		
		// Load tests data from hd.
		/*
		String tests_dir = "D:\\java\\tests\\msmp";
		
		File folder = new File(tests_dir);
		File[] listOfFiles = folder.listFiles();

		int n = listOfFiles.length;
		
		operation = "";
		
		if(n > 0)
		{
			titles = new String[n];
			mss_data = new String[n];
			mps_data = new String[n];
			intervals = new String[n];
			tests_description = new String[n];
		}
		
    	BufferedReader br;
    	String l;
    	int j = 0;
    	int k = 0;
		
		for (File file : listOfFiles) 
		{	
		    if (file.isFile()) 
		    {    	
				try 
				{
					br = new BufferedReader(new FileReader(file));
					k = 0;
					
					while ((l = br.readLine()) != null) 
					{
						if(k == 0)
							titles[j] = l;
						else if(k == 1)
							tests_description[j] = l;
						else if(k == 2)
							mss_data[j] = l;
						else if(k == 3)
							mps_data[j] = l;
						else if(k == 4)
							intervals[j] = l;
						else
						{
							JOptionPane.showMessageDialog(null, "ERR: Invalid tests information!", "Tests", JOptionPane.INFORMATION_MESSAGE);
							load_tests_information = false;
						}
						
						k++;
					}
					
				} catch (FileNotFoundException e1) 
				{
					e1.printStackTrace();
				} catch (IOException e) 
				{
					e.printStackTrace();
				}
				
				j++;
		    }
		}
		*/
		// End Tests data.
		
	    intersection_info = null;
	    solver_execution_time = null;
				
		geom_to_show_id = 0;
		
		geometryFactory = JTSFactoryFinder.getGeometryFactory(null);
	    reader = new WKTReader(geometryFactory);
			    
	    max = 0;
	    	    
		draw_UI();
			
		w_center = (int) (viz_p.getWidth() / 2);
		h_center = (int) (viz_p.getHeight() / 2);
			
		add_listeners();
		draw_geometry();
		
		/*
		if(load_tests_information)
		{
			n = titles.length;
			String[] model = new String[n];
			
			for (int i = 0; i < n; i++)
				model[i] = titles[i];

			tests_cb.setModel(new DefaultComboBoxModel<>(model));
			
        	SimpleAttributeSet just = new SimpleAttributeSet();
        	StyleConstants.setAlignment(just, StyleConstants.ALIGN_JUSTIFIED);
        	
        	StyledDocument doc = test_desc_tp.getStyledDocument();
        	doc.setParagraphAttributes(20, 1,just, false);
        	
        	test_desc_tp.setText(tests_description[tests_cb.getSelectedIndex()]);
		}
		*/
		
		test_desc_tp.setText("Intersection between a MR and a MS.");
	}
	
	public void paint(Graphics g) 
	{
	    super.paint(g);
	    jp.repaint();
	}

	public void draw_geometry()
	{
		viz_p.setLayout(new BorderLayout());
		jp = new DrawGraphs();
		viz_p.add(jp, BorderLayout.CENTER);
	}
	
    private class DrawGraphs extends JPanel
    {
    	private int dx = 0;
    	private int dy = 0;
    	
    	private double sx = 1;
    	private double sy = 1; 	
    	   	
    	private int xx = 0;
    	private int yy = 0;
    	
		private static final long serialVersionUID = 3203545490664689791L;
		
		public DrawGraphs() 
		{
			setBackground(Color.white);
			setAlignmentY(CENTER_ALIGNMENT);
			setAlignmentX(CENTER_ALIGNMENT);
			
			cx = 0;
			cy = 0;

			dx = (int) ((-cx + w_center));
			dy = (int) ((cy + h_center));
			
	        addMouseListener(new MouseAdapter() 
	        {
	            public void mousePressed(MouseEvent e) 
	            {
	            	xx = e.getX();
	            	yy = e.getY();
	            }
	        });

	        addMouseMotionListener(new MouseAdapter() 
	        {
	            public void mouseDragged(MouseEvent e) 
	            {        	
	            	int ddx = (e.getX() - xx);
	            	int ddy = (e.getY() - yy);
	            	
	            	translate(ddx, ddy);
	            	repaint();
	            	
	            	xx = e.getX();
	            	yy = e.getY();
	            }
	        });
	        
	        addMouseWheelListener(new MouseAdapter(){
	            public void mouseWheelMoved(MouseWheelEvent e) 
	            {
    	        
		            int notches = e.getWheelRotation();
					DrawGraphs c = (DrawGraphs) jp;
					
		            if (notches > 0) 
		            {
		            	if (zoomLevel < maxZoomLevel) 
		            	{
		            		zoomLevel += zoomMultiplicationFactor; 
			            	c.scale(zoomMultiplicationFactor, zoomMultiplicationFactor);
			            	c.translate(true);
		            	}
		            } else {
			           	if (zoomLevel > minZoomLevel) 
			           	{
			           		zoomLevel -= zoomMultiplicationFactor;
							c.scale(-zoomMultiplicationFactor, -zoomMultiplicationFactor);
							c.translate(false);
			            }
		            }

		            jp.repaint();
	            }
	        });       
		};
		
        public void reset() 
        {
        	dx = 0;
        	dy = 0;
        	
        	sx = 1;
        	sy = 1; 	
        	   	
        	xx = 0;
        	yy = 0;
        }
		
        public void adjust_screen_position()
        {
			if(mr_p_i == null)
				return;
			
			try {
				geometry = reader.read(mr_p_i[0]);
			} catch (ParseException e) {
				e.printStackTrace();
			}
			
        	if(geometry == null)
        		return;
        	
			Point c = geometry.getCentroid();

			cx = c.getX();
			cy = c.getY();

			w_center = (int) (this.getParent().getWidth() / 2);
			h_center = (int) (this.getParent().getHeight() / 2);
			
			dx = (int) ((-cx + w_center));
			dy = (int) ((cy + h_center));
        }
        
		@Override
        protected void paintComponent(Graphics g)
		{
			super.paintComponent(g);

	        Graphics2D gr = (Graphics2D) g;
	        gr.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
		    gr.setStroke(new BasicStroke(1.0f));	        
		    gr.setPaint(Color.blue);

	        AffineTransform at = new AffineTransform();

	        at.translate(dx, dy);        
	        at.scale(sx, -sy);
	        
	        zoom_level.setText("Zoom Level: " + sx);
	                
			try 
			{
	    		double marker_radius = Double.parseDouble(p_radius_tx.getText());

	    		if(intersection_geom != null)
	    		{
	    			Geometry geom = reader.read(intersection_geom);
    				gr.setPaint(Color.gray);
    				gr.draw(new LiteShape(geom, at, false));
	    		}
	    		
	    		if(mr_p_i != null)
	    		{
	    			Geometry geom;
	    			String v = mr_p_i[geom_to_show_id * Nr + (Nr - 1)];
	    			String info = "O: " + String.valueOf(geom_to_show_id + 1) + " :: ";
	    			
	    			/*
	    			for(int h = 0; h < Nr - 3; h++)
	    			{
	    				geom = reader.read(mr_p_i[geom_to_show_id * Nr + h]);
		    			
		    			if(v.equalsIgnoreCase("0"))
		    			{
		    				info += "False";
		    				gr.setPaint(Color.black);
		    			}
		    			else
		    			{
		    				info += "True";
		    				gr.setPaint(Color.red);
		    			}
		    			
			    		gr.draw(new LiteShape(geom, at, false));
	    			}
	    			*/
	    			
	    			// Region
	    			
    				geom = reader.read(mr_p_i[geom_to_show_id * Nr]);
	    			
	    			if(v.equalsIgnoreCase("0"))
	    			{
	    				info += "False";
	    				gr.setPaint(Color.black);
	    			}
	    			else
	    			{
	    				info += "True";
	    				gr.setPaint(Color.red);
	    			}
	    			
		    		gr.draw(new LiteShape(geom, at, false));
	    			
		    		// Original
		    		 
 		    		LineString l = (LineString) reader.read(mr_p_i[geom_to_show_id * Nr + 2]);
	    			geom = reader.read(mr_p_i[geom_to_show_id * Nr + 2]);
 
		    		if(!geom.isEmpty())
		    		{
		    			//if(v.equalsIgnoreCase("0"))
		    			//	gr.setPaint(Color.blue);
		    			//else
		    			gr.setPaint(Color.black);
		    			
		    			gr.draw(new LiteShape(geom, at, false));

			    		// Draw marker.
			    		
		    			Coordinate c;
		    			GeometricShapeFactory shape_factory;
		    			Geometry circle;
			    		
		    			c = l.getCoordinateN(0);
			    		
			    		shape_factory = new GeometricShapeFactory();
			    		shape_factory.setNumPoints(32);
			    		shape_factory.setCentre(new Coordinate(c.x, c.y));
			    		shape_factory.setSize(marker_radius);
			    		circle = shape_factory.createCircle();
			    		
		    			//if(v.equalsIgnoreCase("0"))
		    			gr.setPaint(Color.black);
		    			//else
		    			//	gr.setPaint(Color.magenta);
			    		
			    		gr.draw(new LiteShape(circle, at, false));
			    				    		
		    			c = l.getCoordinateN(1);
			    		
			    		shape_factory = new GeometricShapeFactory();
			    		shape_factory.setNumPoints(32);
			    		shape_factory.setCentre(new Coordinate(c.x, c.y));
			    		shape_factory.setSize(marker_radius);
			    		circle = shape_factory.createCircle();
			    		
		    			//if(v.equalsIgnoreCase("0"))
		    			gr.setPaint(Color.black);
		    			//else
		    			//	gr.setPaint(Color.magenta);
			    		
			    		gr.draw(new LiteShape(circle, at, false));
		    		}
		    		
		    		// Clipping
		    		
		    		l = (LineString) reader.read(mr_p_i[geom_to_show_id * Nr + 1]);
	    			geom = reader.read(mr_p_i[geom_to_show_id * Nr + 1]);
		    		
		    		if(!geom.isEmpty())
		    		{
		    			if(v.equalsIgnoreCase("0"))
		    				gr.setPaint(Color.black);
		    			else
		    				gr.setPaint(Color.red);
		    			
		    			gr.draw(new LiteShape(geom, at, false));

			    		// Draw marker.
			    		
		    			Coordinate c;
		    			GeometricShapeFactory shape_factory;
		    			Geometry circle;
			    		
		    			c = l.getCoordinateN(0);
			    		
			    		shape_factory = new GeometricShapeFactory();
			    		shape_factory.setNumPoints(32);
			    		shape_factory.setCentre(new Coordinate(c.x, c.y));
			    		shape_factory.setSize(marker_radius);
			    		circle = shape_factory.createCircle();
			    		
		    			if(v.equalsIgnoreCase("0"))
		    				gr.setPaint(Color.black);
		    			else
		    				gr.setPaint(Color.red);
			    		
			    		gr.draw(new LiteShape(circle, at, false));
			    				    		
		    			c = l.getCoordinateN(1);
			    		
			    		shape_factory = new GeometricShapeFactory();
			    		shape_factory.setNumPoints(32);
			    		shape_factory.setCentre(new Coordinate(c.x, c.y));
			    		shape_factory.setSize(marker_radius);
			    		circle = shape_factory.createCircle();
			    		
		    			if(v.equalsIgnoreCase("0"))
		    				gr.setPaint(Color.black);
		    			else
		    				gr.setPaint(Color.red);
			    		
			    		gr.draw(new LiteShape(circle, at, false));
		    		}
		    			    		
		    		Color c = null;
		    		
		    		/*
		    		c = new Color(140, 87, 29);

	    		    gr.setPaint(c);
	    		    gr.setFont(new Font("Arial", Font.BOLD, 14));
	    		    gr.drawString(operation, 20, 30);
		    		*/
		    		
	    		    c = new Color(19, 25, 66);
	    		    gr.setPaint(c);
	    		    gr.setFont(new Font("Arial", Font.BOLD, 14));
	    		    gr.drawString(intersection_info, 20, 50);
	    		    
	    			if(v.equalsIgnoreCase("0"))
	    				gr.setPaint(Color.black);
	    			else
	    				gr.setPaint(Color.magenta);
	    		    
	    		    gr.setFont(new Font("Arial", Font.BOLD, 14));
	    		    gr.drawString(info, 20, 70);
	    		    
	    		    if(solver_execution_time != null)
	    		    {
		    		    gr.setPaint(Color.gray);
		    		    gr.setFont(new Font("Arial", Font.BOLD, 14));
		    		    gr.drawString(solver_execution_time, 20, 90);
	    		    }
	    		}
			} 
			catch (ParseException e) 
			{
				e.printStackTrace();
			}
        };
		
        public void translate(boolean sign) 
        {
        	double cx_star = cx * zoomMultiplicationFactor;
        	double cy_star = cy * zoomMultiplicationFactor;
        	
			if(sign) 
			{
				dx -= (int) cx_star;
				dy += (int) cy_star;				
			}
			else
			{
				dx += (int) cx_star;
				dy -= (int) cy_star;				
			}
        }
        
        public void translate(int x, int y) 
        {
        	dx += x;
        	dy += y;
        }
        
        public void scale(double x, double y) 
        {
        	sx += x;
        	sy += y;
        }
    }
	
	public void draw_UI() 
	{
		setTitle("MR MS Intersection Experiment 1");
		setDefaultCloseOperation(JFrame.DO_NOTHING_ON_CLOSE);
	    setSize(1296, 720);
	    setLocationRelativeTo(null);
	    setExtendedState(f.getExtendedState() | JFrame.MAXIMIZED_BOTH);
	    
		contentPane = new JPanel();
		contentPane.setBorder(new EmptyBorder(5, 5, 5, 5));
		setContentPane(contentPane);
		contentPane.setLayout(null);
		
		viz_p = new JPanel();
		viz_p.setLocation(175, 10);
		
		viz_p.setSize(930, 590);
		
		viz_p.setBackground(Color.WHITE);
		viz_p.setBorder(new LineBorder(Color.black, 1));
		contentPane.add(viz_p);
		
		tools_p = new JPanel();
		tools_p.setBorder(new LineBorder(new Color(0, 0, 0)));
		tools_p.setBounds(10, 616, 1260, 36);
		contentPane.add(tools_p);
		
		gran_tx = new JTextField();
		gran_tx.setText("9");
		gran_tx.setColumns(2);
		tools_p.add(gran_tx);
		
		zoom_out_bt = new JButton("Zoom Out");
		tools_p.add(zoom_out_bt);
		
		zoom_in_bt = new JButton("Zoom In");
		tools_p.add(zoom_in_bt);
		
		save_all_to_png_bt = new JButton("Save All to Png");
		tools_p.add(save_all_to_png_bt);
	
		save_to_picture_bt = new JButton("Save Curr to Png");
		tools_p.add(save_to_picture_bt);
		
		save_picture_to_tx = new JTextField();
		save_picture_to_tx.setText("d:\\\\ex");
		tools_p.add(save_picture_to_tx);
		save_picture_to_tx.setColumns(16);
		
		rate = new JTextField();
		rate.setText("16");
		tools_p.add(rate);
		rate.setColumns(2);
		
		show_m_region_evolution_bt = new JButton("Interpolate");
		tools_p.add(show_m_region_evolution_bt);
		
		show_m_region_evolution_slider = new JSlider();
		show_m_region_evolution_slider.setValue(0);
		tools_p.add(show_m_region_evolution_slider);
		
		show_m_region_evolution_slider.setMinimum(0);
		show_m_region_evolution_slider.setMaximum(max);
		
		status = new JLabel("");
		tools_p.add(status);
		
		show_footprint_bt = new JButton("Show Footprint");
		show_footprint_bt.setEnabled(false);
		show_footprint_bt.setBounds(12, 10, 153, 25);
		contentPane.add(show_footprint_bt);
		
		step = new JTextField();
		step.setEnabled(false);
		step.setText("1");
		step.setBounds(12, 37, 56, 22);
		contentPane.add(step);
		step.setColumns(10);
		
		fill = new JCheckBox("Fill");
		fill.setEnabled(false);
		fill.setBounds(107, 36, 56, 25);
		contentPane.add(fill);
		
		zoom_level = new JLabel("Zoom Level:");
		zoom_level.setBounds(1115, 10, 155, 14);
		contentPane.add(zoom_level);
		
		zoom = new JSlider();
		zoom.setEnabled(false);
		zoom.setValue(1);
		zoom.setMinimum(1);
		zoom.setBounds(1115, 38, 155, 26);
		contentPane.add(zoom);
		
		n_samples = new JLabel("N\u00BA Samples: ");
		n_samples.setBounds(1115, 73, 155, 14);
		contentPane.add(n_samples);
		
	    n_samples.setText("N� Samples: 0");
	    
	    n_samples_tx = new JTextField();
	    n_samples_tx.setToolTipText("Number of samples for vizualisation.");
	    n_samples_tx.setText("100");
	    n_samples_tx.setBounds(10, 394, 65, 20);
	    contentPane.add(n_samples_tx);
	    n_samples_tx.setColumns(10);
	    
	    reset_bt = new JButton("Reset");
	    reset_bt.setFont(new Font("Tahoma", Font.BOLD, 11));
	    reset_bt.setForeground(new Color(0, 0, 128));
	    reset_bt.setBounds(10, 578, 155, 23);
	    contentPane.add(reset_bt);
	    
	    i_e_tx = new JTextField();
	    i_e_tx.setToolTipText("Final instant of the interval considered.");
	    i_e_tx.setBackground(SystemColor.control);
	    i_e_tx.setText("2000");
	    i_e_tx.setBounds(100, 415, 64, 20);
	    contentPane.add(i_e_tx);
	    i_e_tx.setColumns(10);
	    
	    i_b_tx = new JTextField();
	    i_b_tx.setToolTipText("Initial instant of the interval considered.");
	    i_b_tx.setBackground(SystemColor.control);
	    i_b_tx.setForeground(Color.BLACK);
	    i_b_tx.setText("1000");
	    i_b_tx.setBounds(10, 415, 65, 20);
	    contentPane.add(i_b_tx);
	    i_b_tx.setColumns(10);
	    
	    mr_p_i_bt = new JButton("Query");
	    mr_p_i_bt.setToolTipText("Load the moving objects.");
	    mr_p_i_bt.setFont(new Font("Tahoma", Font.BOLD, 11));
	    mr_p_i_bt.setBounds(8, 128, 155, 23);
	    contentPane.add(mr_p_i_bt);
	    
	    mr_p_tx = new JTextArea();
	    mr_p_tx.setToolTipText("MR initial observation.");
	    mr_p_tx.setBackground(Color.WHITE);
	    mr_p_tx.setText("POLYGON((975.0420063220051 697.090167065809, 968.2376237623762 719.366754617414, 949.8141049487542 719.682075626039, 947.5206593693675 726.5578738835004, 929.1730947342762 738.0175376459358, 929.5007298170459 743.256241080192, 924.3364137823626 741.690195051915, 919.6716773339609 738.3449566105769, 912.7913405958017 741.619146256987, 901.9793828644084 732.4514152470385, 891.8226952985542 721.3191704492442, 884.6147234776257 716.73530494427, 877.4067516566968 712.1514394392957, 873.1474955806933 721.3191704492442, 868.8882395046899 730.4869014591925, 851.6435643564355 749.7625329815303, 845.7678029771724 751.5623397481193, 839.0734469726663 758.972351382961, 829.2443944895814 769.7771772161138, 823.6745980825001 760.609446206166, 814 751.4999999999998, 811.0891089108911 744.6965699208442, 802.3783177024834 736.3804428227309, 798 736, 769.3716535620496 707.0652770818208, 757.5275973847811 695.0944675046978, 734.5578555691986 671.8789067884509, 719.8142768445714 645.3579706525286, 721.7800873411885 635.8628206779392, 723.7458978378055 621.1289672690934, 735.4026288700353 597.7088326122334, 738 589, 763.0621077701443 576.5999880779154, 814 568, 845.6261486280558 565.4677432801209, 852 570, 878.7172919877744 575.2903122193516, 892.7049504950495 586.1319261213721, 901.829702970297 592.211081794195, 907.3811614420508 597.0972549398289, 928 614.0000000000002, 975.0420063220051 697.090167065809))");
	    mr_p_tx.setBounds(8, 154, 155, 36);
	    contentPane.add(mr_p_tx);
	    
	    mp1_data_tx = new JTextArea();
	    mp1_data_tx.setToolTipText("MP1 trajectory.");
	    mp1_data_tx.setBackground(Color.WHITE);
	    mp1_data_tx.setText("755,489#895,774#1000,2000");
	    mp1_data_tx.setBounds(8, 235, 155, 36);
	    contentPane.add(mp1_data_tx);
	    
	    pass_through_control_points_cb = new JCheckBox("Pass T. Control Points");
	    pass_through_control_points_cb.setToolTipText("Curve passes through all the control points.");
	    pass_through_control_points_cb.setSelected(true);
	    pass_through_control_points_cb.setBounds(10, 329, 155, 23);
	    contentPane.add(pass_through_control_points_cb);
	    
	    print_intersection_information_cb = new JCheckBox("Show Intersection I.");
	    print_intersection_information_cb.setToolTipText("Show intersection information.");
	    print_intersection_information_cb.setSelected(true);
	    print_intersection_information_cb.setBounds(10, 348, 155, 23);
	    contentPane.add(print_intersection_information_cb);
	    
	    print_solver_execution_time_cb = new JCheckBox("Show Solver I.");
	    print_solver_execution_time_cb.setToolTipText("Show solver execution information.");
	    print_solver_execution_time_cb.setSelected(true);
	    print_solver_execution_time_cb.setBounds(10, 367, 155, 23);
	    contentPane.add(print_solver_execution_time_cb);
	    
	    p_radius_tx = new JTextField();
	    p_radius_tx.setToolTipText("Moving point marker radius.");
	    p_radius_tx.setBackground(new Color(255, 255, 240));
	    p_radius_tx.setText("5");
	    p_radius_tx.setBounds(10, 436, 65, 20);
	    contentPane.add(p_radius_tx);
	    p_radius_tx.setColumns(10);
	    
	    JLabel tests_lb = new JLabel("Predicates:");
	    tests_lb.setForeground(new Color(25, 25, 112));
	    tests_lb.setFont(new Font("Tahoma", Font.BOLD, 12));
	    tests_lb.setBounds(10, 81, 155, 25);
	    contentPane.add(tests_lb);
	    
	    JLabel test_desc_lb = new JLabel("Test Description:");
	    test_desc_lb.setFont(new Font("Tahoma", Font.BOLD, 12));
	    test_desc_lb.setBounds(1115, 96, 155, 22);
	    contentPane.add(test_desc_lb);
	    
	    test_desc_tp = new JTextPane();
	    test_desc_tp.setBackground(new Color(245, 255, 250));
	    test_desc_tp.setBounds(1115, 123, 155, 222);
	    contentPane.add(test_desc_tp);
	    
	    s_precision_tx = new JTextField();
	    s_precision_tx.setBackground(SystemColor.text);
	    s_precision_tx.setToolTipText("Spatial precision.");
	    s_precision_tx.setText("0.0000001");
	    s_precision_tx.setBounds(10, 457, 65, 20);
	    contentPane.add(s_precision_tx);
	    s_precision_tx.setColumns(10);
	    
	    n_dec_dig_tx = new JTextField();
	    n_dec_dig_tx.setBackground(new Color(245, 255, 250));
	    n_dec_dig_tx.setToolTipText("Number of decimal  digits.");
	    n_dec_dig_tx.setText("2");
	    n_dec_dig_tx.setBounds(100, 457, 65, 20);
	    contentPane.add(n_dec_dig_tx);
	    n_dec_dig_tx.setColumns(10);
	    
	    op_cb = new JComboBox<>();
	    op_cb.setEnabled(false);
	    op_cb.setModel(new DefaultComboBoxModel(new String[] {"Intersects", "Touches (Meets)", "Equals", "Disjoint", "Contains", "Within (Inside)", "Intersection"}));
	    op_cb.setSelectedIndex(0);
	    op_cb.setBounds(8, 107, 155, 20);
	    contentPane.add(op_cb);
	    
	    mr_q_tx = new JTextArea();
	    mr_q_tx.setText("POLYGON((965 635, 963.1683168316831 648.4432717678101, 958.0990099009902 658.5751978891822, 947.960396039604 658.5751978891822, 942 675, 932 679, 933.5 683.9999999999998, 935 689, 919.2997169901681 692.9781016562131, 907.4059405940594 688.9709762532982, 897.2673267326733 683.9050131926122, 884.6074998412831 681.6848638401293, 875 680, 875.5385318320745 694.8658276536648, 871 710, 861.6493140294922 728.7013719410154, 858.3483767115072 735.028033248251, 855.0474393935223 741.3546945554867, 851.6115528967149 747.7221555823205, 837.1294340674169 742.0589775899646, 826.2970297029703 734.5646437994724, 816.1584158415842 729.4986807387863, 810.6838257704394 731.3618636044034, 793.0534202391211 721.608612617568, 772.9043853461864 709.6530146337057, 755.3267326732673 704.1688654353561, 741 698, 724.9108910891089 688.9709762532982, 704.6336633663364 668.707124010554, 703 651.0000000000002, 702.6975918911147 637.9194267305304, 705 626, 714.7722772277225 602.8496042216359, 760 570, 795.8811881188119 552.1899736147757, 834.2959760355977 574.0513638167383, 846.5742574257424 562.3218997361478, 878 573.0000000000002, 887.1287128712871 572.4538258575199, 902.3366336633663 582.5857519788917, 950.7825840103793 618.7275457564351, 965 635))");
	    mr_q_tx.setToolTipText("MR final observation.");
	    mr_q_tx.setBackground(new Color(245, 245, 220));
	    mr_q_tx.setBounds(8, 194, 155, 36);
	    contentPane.add(mr_q_tx);
	    
	    mp2_data_tx = new JTextArea();
	    mp2_data_tx.setToolTipText("MP2 trajectory.");
	    mp2_data_tx.setText("725,439#875,734#1000,2000");
	    mp2_data_tx.setBackground(new Color(245, 245, 220));
	    mp2_data_tx.setBounds(8, 276, 155, 36);
	    contentPane.add(mp2_data_tx);
	}

	public void add_listeners()
	{
        addWindowListener(new WindowAdapter() 
        {
            @Override
            public void windowClosing(WindowEvent e) 
            {
                setVisible(false);
            }
        });
        
    	save_all_to_png_bt.addActionListener(new ActionListener() 
		{
			public void actionPerformed(ActionEvent arg0) 
			{
				if(mr_p_i == null)
					return;
				
				show_m_region_evolution_slider.setEnabled(false);
				
				int v = geom_to_show_id;
				int N = mr_p_i.length / 4;
				
				status.setText("Saving!");
				
				//JOptionPane.showMessageDialog(null, "Click to start!", "Save", JOptionPane.INFORMATION_MESSAGE);
				
				try
				{
					int granularity = Integer.parseInt(gran_tx.getText());
					
					for(int i = 0; i < N; i = i + granularity) 
					{						
						geom_to_show_id = i;
			    		jp.repaint();
			    		
						BufferedImage bi = ScreenImage.createImage(viz_p);
	    				ScreenImage.writeImage(bi, save_picture_to_tx.getText() + "_" + (N + i) + ".png");
					}
    			} 
				catch (IOException ex) {
    				ex.printStackTrace();
    			}
				
				geom_to_show_id = v;
				jp.repaint();
				
				JOptionPane.showMessageDialog(null, "Saved!", "Save", JOptionPane.INFORMATION_MESSAGE);	
				
				show_m_region_evolution_slider.setEnabled(true);
				status.setText("");
			}
		});
        
        /*
        tests_cb.addActionListener (new ActionListener () 
        {
            public void actionPerformed(ActionEvent e) 
            {
            	test_desc_tp.setText(tests_description[tests_cb.getSelectedIndex()]);
            }
        });
        */
		
		show_footprint_bt.addActionListener(new ActionListener() 
		{
			public void actionPerformed(ActionEvent arg0) 
			{
				/*
				if(show_footprint) {
					show_footprint = false;
					return;
				}
				
				show_m_region_evolution_bt.setEnabled(false);
				show_m_region_evolution_slider.setEnabled(false);
				save_to_picture_bt.setEnabled(false);
				
			    show_granularity = Integer.parseInt(step.getText());
			    show_footprint = true;
				
				geom_to_show_id = 0;

			    play_task = new TimerTask() 
			    {
			        public void run() 
			        {
			        	jp.repaint();
			        	
			    		if(geom_to_show_id < max) 
			    			geom_to_show_id += show_granularity;	    			
			    		else 
			    		{
			    			timer.cancel();
			    			
							show_m_region_evolution_slider.setValue(show_m_region_evolution_slider.getMaximum());
							show_m_region_evolution_bt.setEnabled(true);
							show_m_region_evolution_slider.setEnabled(true);
							save_to_picture_bt.setEnabled(true);
			    		}
			        }
			    };
			    
				timer = new Timer();
				timer.scheduleAtFixedRate(play_task, 0, Long.parseLong(rate.getText()));
				*/
			}
		});
        
    	zoom_out_bt.addActionListener(new ActionListener() 
    	{
			public void actionPerformed(ActionEvent arg0) 
			{
				DrawGraphs c = (DrawGraphs) jp;

	           	if (zoomLevel > minZoomLevel) 
	           	{
	           		zoomLevel -= zoomMultiplicationFactor;
					c.scale(-zoomMultiplicationFactor, -zoomMultiplicationFactor);
					c.translate(false);
	            }

	            jp.repaint();
			}
		});
    	
    	zoom_in_bt.addActionListener(new ActionListener() 
    	{
			public void actionPerformed(ActionEvent arg0) 
			{
				DrawGraphs c = (DrawGraphs) jp;

            	if (zoomLevel < maxZoomLevel) 
            	{
            		zoomLevel += zoomMultiplicationFactor; 
	            	c.scale(zoomMultiplicationFactor, zoomMultiplicationFactor);
	            	c.translate(true);
            	}

	            jp.repaint();

			}
		});
    	
    	/*
    	mr_p_i_bt.addActionListener(new ActionListener() 
    	{
			public void actionPerformed(ActionEvent arg0) 
			{
				mr_p_i = null;

				String ms_data = mr_p_tx.getText();
				String mp_data = mp_data_tx.getText();
				
				boolean pass_through_control_points = pass_through_control_points_cb.isSelected();
				boolean show_intersection_information = print_intersection_information_cb.isSelected();
				boolean show_solver_exec_time = print_solver_execution_time_cb.isSelected();
				
				int num_samples = Integer.parseInt(n_samples_tx.getText());
				String interval = i_b_tx.getText() + "," + i_e_tx.getText();

				String prec = s_precision_tx.getText();
				String n_dec_dig = n_dec_dig_tx.getText();
				
				int op_id = op_cb.getSelectedIndex();
				
				String op = String.valueOf(op_id + 1);

				if(op_id == 0)
					operation = "Intersect(MS, MP, I)";
				else if(op_id == 1)
					operation = "Touch(MS, MP, I)";
				else if(op_id == 2)
					operation = "Equal(MS, MP, I)";
				else if(op_id == 3)
					operation = "Disjoint(MS, MP, I)";
				else if(op_id == 4)
					operation = "Contains(MS, MP, I)";
				else if(op_id == 5)
					operation = "Within(MP, MS, I)";
				else {
					JOptionPane.showMessageDialog(null, "Operation unknown or mot implemented/applicable.", "Operation", JOptionPane.INFORMATION_MESSAGE);
					jp.repaint();
					return;
				}
				
				String[] cmd = new String[12];
				
				cmd[0] = "python";
				cmd[1] = "D:\\java\\tests.py";
				cmd[2] = ms_data;
				cmd[3] = mp_data;
				
				if(pass_through_control_points)
					cmd[4] = "1";
				else
					cmd[4] = "0";
				
				if(show_intersection_information)
					cmd[5] = "1";
				else
					cmd[5] = "0";
				
				if (show_solver_exec_time)
					cmd[6] = "1";
				else
					cmd[6] = "0";
				
				cmd[7] = String.valueOf(num_samples);
				cmd[8] = interval;
				cmd[9] = prec;
				cmd[10] = n_dec_dig;
				cmd[11] = op;
				
				Runtime rt = Runtime.getRuntime();
				Process pr = null;
				
				try
				{
					pr = rt.exec(cmd);
				}
				catch (IOException e1) 
				{
					e1.printStackTrace();
				}
				
				BufferedReader bfr = new BufferedReader(new InputStreamReader(pr.getInputStream()));
				String line = "";
				
				String[] arr = new String[1000];
				int i = 0;
				
				try
				{
					while((line = bfr.readLine()) != null)
					{
						arr[i] = line;
						i++;
					}
				}
				catch (IOException e1)
				{
					e1.printStackTrace();
				}
				
				if(i == 1)
				{
					JOptionPane.showMessageDialog(null, arr[0], "Intersection", JOptionPane.INFORMATION_MESSAGE);
					jp.repaint();
					return;
				}
				
				solver_execution_time = null;
				mr_p_i_len = i;
				
				int m = 1;
				
				if (show_solver_exec_time)
				    m = 2;
				
				mr_p_i = new String[mr_p_i_len - m];
				
				for(int k = 0; k < mr_p_i_len - m; k++)
					mr_p_i[k] = arr[k];
				
				if (show_solver_exec_time)
					solver_execution_time = arr[mr_p_i_len - 1];
				
				intersection_info = arr[mr_p_i_len - m];
				
				max = mr_p_i.length / 3;
				
				n_samples.setText("N� Samples: " + String.valueOf(max));
				
				show_m_region_evolution_slider.setMinimum(0);
				show_m_region_evolution_slider.setMaximum(max);
				
				Nr = 3;
				
    			((DrawGraphs) jp).reset();
    			((DrawGraphs) jp).adjust_screen_position();		
	            jp.repaint();
			}
		});
		*/
    	
    	mr_p_i_bt.addActionListener(new ActionListener() 
    	{
			public void actionPerformed(ActionEvent arg0) 
			{
				mr_p_i = null;

				//int idx = tests_cb.getSelectedIndex();
								
				boolean pass_through_control_points = pass_through_control_points_cb.isSelected();
				boolean show_intersection_information = print_intersection_information_cb.isSelected();
				boolean show_solver_exec_time = print_solver_execution_time_cb.isSelected();
				
				int num_samples = Integer.parseInt(n_samples_tx.getText());
				String interval = i_b_tx.getText() + "," + i_e_tx.getText();

				String prec = s_precision_tx.getText();
				String n_dec_dig = n_dec_dig_tx.getText();
				
				int op_id = op_cb.getSelectedIndex();
				
				String op = null;
				
				if(op_id >= 6)
					op = String.valueOf(op_id + 3);
				else
					op = String.valueOf(op_id + 1);
				
				/*
				if(op_id == 0)
					operation = "Intersect(MR, MP, I)";
				else if(op_id == 1)
					operation = "Touch(MP, MR, I)";
				else if(op_id == 2)
					operation = "Equal(MR, MP, I)";
				else if(op_id == 3)
					operation = "Disjoint(MR, MP, I)";
				else if(op_id == 4)
					operation = "Contains(MR, MP, I)";
				else if(op_id == 5)
					operation = "Within(MP, MR, I)";
				else if(op_id == 6)
					operation = "Intersection(MP, MR, I)";
				else {
					JOptionPane.showMessageDialog(null, "Operation mot implemented.", "Operation", JOptionPane.INFORMATION_MESSAGE);
					jp.repaint();
					return;
				}
				*/
				
				String[] cmd = new String[14];
				
				cmd[0] = "python";
				cmd[1] = "/home/user/STExperiments/scripts/mr_ms_exp_pred1.py";
				
				cmd[2] = mr_p_tx.getText();
				cmd[3] = mr_q_tx.getText();
				
				//cmd[2] = mss_data[idx];
				//cmd[4] = mps_data[idx];
				
				cmd[4] = mp1_data_tx.getText();
				cmd[5] = mp2_data_tx.getText();
				
				if(pass_through_control_points)
					cmd[6] = "1";
				else
					cmd[6] = "0";
				
				if(show_intersection_information)
					cmd[7] = "1";
				else
					cmd[7] = "0";
				
				if (show_solver_exec_time)
					cmd[8] = "1";
				else
					cmd[8] = "0";
				
				cmd[9] = String.valueOf(num_samples);
				//cmd[9] = intervals[idx];
				cmd[10] = interval;
				cmd[11] = prec;
				cmd[12] = n_dec_dig;
				cmd[13] = op;
				
				Runtime rt = Runtime.getRuntime();
				Process pr = null;
				
				try
				{
					pr = rt.exec(cmd);
				}
				catch (IOException e1) 
				{
					e1.printStackTrace();
				}
				
				BufferedReader bfr = new BufferedReader(new InputStreamReader(pr.getInputStream()));
				String line = "";
				
				String[] arr = new String[num_samples * 5];
				int i = 0;
				
				try
				{
					while((line = bfr.readLine()) != null)
					{
						arr[i] = line;
						i++;
					}
				}
				catch (IOException e1)
				{
					e1.printStackTrace();
				}
				
				if(i == 1)
				{
					JOptionPane.showMessageDialog(null, arr[0], "MR. MP. Predicates", JOptionPane.INFORMATION_MESSAGE);
					jp.repaint();
					return;
				}
				
				//System.out.println(i);
				
				if(i == 4 || i == 6)
				{
					String err_msg = arr[3];
					
					JOptionPane.showMessageDialog(null, err_msg, "MR. MP. Predicates", JOptionPane.INFORMATION_MESSAGE);
					jp.repaint();
					return;
				}				
				
				solver_execution_time = null;
				mr_p_i_len = i;
				
				int m = 1;
				
				if (show_solver_exec_time)
				    m = 2;
				
				if(op_id == 6)
				{
					m = 3;
					
					mr_p_i = new String[mr_p_i_len - m];
					
					for(int k = 0; k < mr_p_i_len - m; k++)
						mr_p_i[k] = arr[k];
					
					if (show_solver_exec_time)
						solver_execution_time = arr[mr_p_i_len - 2];
					
					intersection_info = arr[mr_p_i_len - m];
					intersection_geom = arr[mr_p_i_len - 1];					
				}
				else
				{
					mr_p_i = new String[mr_p_i_len - m];
					
					for(int k = 0; k < mr_p_i_len - m; k++)
						mr_p_i[k] = arr[k];
					
					if (show_solver_exec_time)
						solver_execution_time = arr[mr_p_i_len - 1];
					
					intersection_info = arr[mr_p_i_len - m];
					intersection_geom = null;					
				}
				
				/*
				mr_p_i = new String[mr_p_i_len - m];
				
				for(int k = 0; k < mr_p_i_len - m; k++)
					mr_p_i[k] = arr[k];
				
				if (show_solver_exec_time)
					solver_execution_time = arr[mr_p_i_len - 1];
				
				intersection_info = arr[mr_p_i_len - m];
				*/
				
				max = mr_p_i.length / 4;

				n_samples.setText("N� Samples: " + String.valueOf(max));
				
				show_m_region_evolution_slider.setMinimum(0);
				show_m_region_evolution_slider.setMaximum(max);
				
				Nr = 4;

				//System.out.println(max);
				//for(int k = 0; k < mr_p_i.length; k++)
				//	System.out.println(mr_p_i[k]);				
				
    			((DrawGraphs) jp).reset();
    			((DrawGraphs) jp).adjust_screen_position();		
	            jp.repaint();
			}
		});
    	
 		save_to_picture_bt.addActionListener(new ActionListener() 
		{
			public void actionPerformed(ActionEvent arg0) 
			{
				String filename = save_picture_to_tx.getText() + ".png";
				
				try
				{
					BufferedImage bi = ScreenImage.createImage(viz_p);
    				ScreenImage.writeImage(bi, filename);
    			} 
				catch (IOException ex) {
    				ex.printStackTrace();
    			}
							
				JOptionPane.showMessageDialog(null, "Saved to " + filename + ".", "Save", JOptionPane.INFORMATION_MESSAGE);	
			}
		});
		
		show_m_region_evolution_bt.addActionListener(new ActionListener() 
		{
			public void actionPerformed(ActionEvent arg0) 
			{
				 if(mr_p_i == null)
					 return;
				
				show_m_region_evolution_bt.setEnabled(false);
				show_m_region_evolution_slider.setEnabled(false);
				save_to_picture_bt.setEnabled(false);		
				geom_to_show_id = 0;
				
			    play_task = new TimerTask() 
			    {
			        public void run() 
			        {
			        	jp.repaint();
			        	
			    		if(geom_to_show_id < max - 1) 
			    			geom_to_show_id++;	    			
			    		else {
			    			timer.cancel();
			    			
							show_m_region_evolution_slider.setValue(show_m_region_evolution_slider.getMaximum());
							show_m_region_evolution_bt.setEnabled(true);
							show_m_region_evolution_slider.setEnabled(true);
							save_to_picture_bt.setEnabled(true);
			    		}
			    		
			        	//System.out.println(geom_to_show_id);
			        	//System.out.println(max);
			        }
			    };
			    
				timer = new Timer();
				timer.scheduleAtFixedRate(play_task, 0, Long.parseLong(rate.getText()));
			}
		});
		
		show_m_region_evolution_slider.addChangeListener(new ChangeListener() 
		{
		    public void stateChanged(ChangeEvent e) 
		    {
		        JSlider s = (JSlider) e.getSource();
		        int i = (int) s.getValue();
		        
		        if(mr_p_i != null)
		        {
			        int n = mr_p_i.length / 4;
			        
			    	if(i < n)
			    		geom_to_show_id = i;
			    	else if(i == n)
			    		geom_to_show_id = i - 1;
		        }
		        
		    	jp.repaint();
		    }
		});
		
		reset_bt.addActionListener(new ActionListener() 
		{
			public void actionPerformed(ActionEvent arg0) 
		    {
				mr_p_i = null;
				intersection_geom = null;
				
		    	jp.repaint();
		    }
		});
	}
}