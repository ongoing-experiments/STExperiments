package gui;

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

public class MRMR extends JFrame 
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
    private JButton query_bt;
    private String intersection_info;
    private String solver_execution_time;
    private JCheckBox print_solver_execution_time_cb;
    private JTextArea p1;
    private JTextArea q1;
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
    private JTextArea P2;
    private JTextArea Q2;
    private JButton i1;
    private JButton i2;
    private JButton i3;	 
    private JButton i4;
    private JButton i5;
    private JButton i6;
    private JButton leg_bt;
    private boolean show_leg;
    private JButton save_all_to_png_bt;
    private JTextField gran_tx;
    private boolean show_footprint;
    private int show_granularity;
    private JButton btn_Intersects;
	private String execution_time;
	private String predicate;
	private boolean shoe_predicate_info;
	
	public MRMR(Data d) 
	{	
		mr_p_i = null;
		Nr = 0;
		f = this;
		show_footprint = false;
		
		//boolean load_tests_information = true;
		
		show_leg = true;
		
		execution_time = null;
		predicate = null;
		shoe_predicate_info = false;
		
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

			//tests_cb.setModel(new DefaultComboBoxModel<>(model));
			
        	SimpleAttributeSet just = new SimpleAttributeSet();
        	StyleConstants.setAlignment(just, StyleConstants.ALIGN_JUSTIFIED);
        	
        	StyledDocument doc = test_desc_tp.getStyledDocument();
        	doc.setParagraphAttributes(20, 1,just, false);
        	
        	//test_desc_tp.setText(tests_description[tests_cb.getSelectedIndex()]);
		}
		*/
		
		test_desc_tp.setText("MR A and MR B initially intersect and become disjoint.");
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
				if(show_footprint && mr_p_i != null)
				{
					Geometry geom;
			    	for(int i = 0; i <= geom_to_show_id; i = i + show_granularity) 
			    	{
			    		
			    		geom = reader.read(mr_p_i[i * Nr]);
			    		
		    			gr.setPaint(Color.black);
				    	gr.draw(new LiteShape(geom, at, false));			    		
			    		
	   					if(fill.isSelected())
	   					{
			   		        for (int j = 0; j < geom.getNumGeometries(); j++)
					   			gr.fill(new LiteShape(geom.getGeometryN(j), at, false));
	   					}
			    	}
				}
				
				else if(mr_p_i != null)
	    		{
	    			Geometry geom0 = reader.read(mr_p_i[geom_to_show_id * Nr]);
	    			Geometry geom1 = reader.read(mr_p_i[geom_to_show_id * Nr + 1]);
	    			
	    			String v = mr_p_i[geom_to_show_id * Nr + (Nr - 1)];
	    			String info = "O: " + String.valueOf(geom_to_show_id + 1) + " :: ";
	    					    			
		    		if(v.equalsIgnoreCase("0"))
		    		{
		    			info += "False";
		    			gr.setPaint(Color.black);
				    	gr.draw(new LiteShape(geom0, at, false));
				    	
		    			gr.setPaint(Color.blue);
		    			gr.draw(new LiteShape(geom1, at, false));				    	
		    		}
		    		else
		    		{
		    			info += "True";
		    			gr.setPaint(Color.red);
		    			
				    	gr.draw(new LiteShape(geom0, at, false));
				    	gr.draw(new LiteShape(geom1, at, false));		    			
		    		}

					if(show_leg)
					{
		    		    gr.setPaint(Color.black);
		    		    gr.setFont(new Font("Arial", Font.BOLD, 14));
		    		    gr.drawString("MR A (Iceberg)", 20, 100);
		    		    
		    		    gr.setPaint(Color.blue);
		    		    gr.setFont(new Font("Arial", Font.BOLD, 14));
		    		    gr.drawString("MR B", 20, 120);
					}
					
					if(shoe_predicate_info)
					{
		    		    gr.setPaint(Color.black);
		    		    gr.setFont(new Font("Arial", Font.BOLD, 14));
		    		    gr.drawString("Intersects: " + predicate, 20, 140);

		    		    gr.setPaint(Color.blue);
		    		    gr.setFont(new Font("Arial", Font.BOLD, 14));
		    		    gr.drawString(execution_time, 20, 160);
					}

			    	Color c = null;
		    		//c = new Color(140, 87, 29);
		    		
	    		    c = new Color(19, 25, 66);
	    		    gr.setPaint(c);
	    		    gr.setFont(new Font("Arial", Font.BOLD, 14));
	    		    gr.drawString(intersection_info, 20, 30);
	    		    
	    			if(v.equalsIgnoreCase("0"))
	    				gr.setPaint(Color.black);
	    			else
	    				gr.setPaint(Color.magenta);
	    		    
	    		    gr.setFont(new Font("Arial", Font.BOLD, 14));
	    		    gr.drawString(info, 20, 50);
	    		    
	    		    if(solver_execution_time != null)
	    		    {
		    		    gr.setPaint(Color.gray);
		    		    gr.setFont(new Font("Arial", Font.BOLD, 14));
		    		    gr.drawString(solver_execution_time, 20, 70);
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
		setTitle("MR MR: Study of Approximation Curves");
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
		
		save_all_to_png_bt = new JButton("Save All to PNG");
		tools_p.add(save_all_to_png_bt);
	
		save_to_picture_bt = new JButton("Save Curr to PNG");
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
		show_footprint_bt.setBounds(12, 10, 153, 25);
		contentPane.add(show_footprint_bt);
		
		step = new JTextField();
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
		
	    n_samples.setText("Nº Samples: 0");
	    
	    n_samples_tx = new JTextField();
	    n_samples_tx.setToolTipText("Number of samples for vizualisation.");
	    n_samples_tx.setText("100");
	    n_samples_tx.setBounds(10, 387, 65, 20);
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
	    i_e_tx.setBounds(100, 412, 64, 20);
	    contentPane.add(i_e_tx);
	    i_e_tx.setColumns(10);
	    
	    i_b_tx = new JTextField();
	    i_b_tx.setToolTipText("Initial instant of the interval considered.");
	    i_b_tx.setBackground(SystemColor.control);
	    i_b_tx.setForeground(Color.BLACK);
	    i_b_tx.setText("1000");
	    i_b_tx.setBounds(10, 412, 65, 20);
	    contentPane.add(i_b_tx);
	    i_b_tx.setColumns(10);
	    
	    query_bt = new JButton("Query");
	    query_bt.setToolTipText("Execute Query");
	    query_bt.setFont(new Font("Tahoma", Font.BOLD, 11));
	    query_bt.setBounds(10, 127, 155, 23);
	    contentPane.add(query_bt);
	    
	    p1 = new JTextArea();
	    p1.setText("POLYGON((975.0420063220051 697.090167065809, 968.2376237623762 719.366754617414, 949.8141049487542 719.682075626039, 947.5206593693675 726.5578738835004, 929.1730947342762 738.0175376459358, 929.5007298170459 743.256241080192, 924.3364137823626 741.690195051915, 919.6716773339609 738.3449566105769, 912.7913405958017 741.619146256987, 901.9793828644084 732.4514152470385, 891.8226952985542 721.3191704492442, 884.6147234776257 716.73530494427, 877.4067516566968 712.1514394392957, 873.1474955806933 721.3191704492442, 868.8882395046899 730.4869014591925, 851.6435643564355 749.7625329815303, 845.7678029771724 751.5623397481193, 839.0734469726663 758.972351382961, 829.2443944895814 769.7771772161138, 823.6745980825001 760.609446206166, 814 751.4999999999998, 811.0891089108911 744.6965699208442, 802.3783177024834 736.3804428227309, 798 736, 769.3716535620496 707.0652770818208, 757.5275973847811 695.0944675046978, 734.5578555691986 671.8789067884509, 719.8142768445714 645.3579706525286, 721.7800873411885 635.8628206779392, 723.7458978378055 621.1289672690934, 735.4026288700353 597.7088326122334, 738 589, 763.0621077701443 576.5999880779154, 814 568, 845.6261486280558 565.4677432801209, 852 570, 878.7172919877744 575.2903122193516, 892.7049504950495 586.1319261213721, 901.829702970297 592.211081794195, 907.3811614420508 597.0972549398289, 928 614.0000000000002, 975.0420063220051 697.090167065809))");
	    p1.setToolTipText("Moving segment data.");
	    p1.setBackground(SystemColor.controlLtHighlight);
	    p1.setBounds(10, 153, 155, 36);
	    contentPane.add(p1);
	    
	    q1 = new JTextArea();
	    q1.setToolTipText("Moving point data.");
	    q1.setBackground(new Color(230, 230, 250));
	    q1.setText("POLYGON((965 635, 963.1683168316831 648.4432717678101, 958.0990099009902 658.5751978891822, 947.960396039604 658.5751978891822, 942 675, 932 679, 933.5 683.9999999999998, 935 689, 919.2997169901681 692.9781016562131, 907.4059405940594 688.9709762532982, 897.2673267326733 683.9050131926122, 884.6074998412831 681.6848638401293, 875 680, 875.5385318320745 694.8658276536648, 871 710, 861.6493140294922 728.7013719410154, 858.3483767115072 735.028033248251, 855.0474393935223 741.3546945554867, 851.6115528967149 747.7221555823205, 837.1294340674169 742.0589775899646, 826.2970297029703 734.5646437994724, 816.1584158415842 729.4986807387863, 810.6838257704394 731.3618636044034, 793.0534202391211 721.608612617568, 772.9043853461864 709.6530146337057, 755.3267326732673 704.1688654353561, 741 698, 724.9108910891089 688.9709762532982, 704.6336633663364 668.707124010554, 703 651.0000000000002, 702.6975918911147 637.9194267305304, 705 626, 714.7722772277225 602.8496042216359, 760 570, 795.8811881188119 552.1899736147757, 834.2959760355977 574.0513638167383, 846.5742574257424 562.3218997361478, 878 573.0000000000002, 887.1287128712871 572.4538258575199, 902.3366336633663 582.5857519788917, 950.7825840103793 618.7275457564351, 965 635))");
	    q1.setBounds(10, 192, 155, 36);
	    contentPane.add(q1);
	    
	    pass_through_control_points_cb = new JCheckBox("Pass T. Control Points");
	    pass_through_control_points_cb.setToolTipText("Curve passes through all the control points.");
	    pass_through_control_points_cb.setSelected(true);
	    pass_through_control_points_cb.setBounds(10, 322, 155, 23);
	    contentPane.add(pass_through_control_points_cb);
	    
	    print_intersection_information_cb = new JCheckBox("Show Intersection I.");
	    print_intersection_information_cb.setToolTipText("Show intersection information.");
	    print_intersection_information_cb.setSelected(true);
	    print_intersection_information_cb.setBounds(10, 341, 155, 23);
	    contentPane.add(print_intersection_information_cb);
	    
	    print_solver_execution_time_cb = new JCheckBox("Show Solver I.");
	    print_solver_execution_time_cb.setToolTipText("Show solver execution information.");
	    print_solver_execution_time_cb.setSelected(true);
	    print_solver_execution_time_cb.setBounds(10, 360, 155, 23);
	    contentPane.add(print_solver_execution_time_cb);
	    
	    JLabel pred_lb = new JLabel("Predicates:");
	    pred_lb.setForeground(new Color(25, 25, 112));
	    pred_lb.setFont(new Font("Tahoma", Font.BOLD, 12));
	    pred_lb.setBounds(10, 81, 155, 25);
	    contentPane.add(pred_lb);
	    
	    JLabel test_desc_lb = new JLabel("Test Description:");
	    test_desc_lb.setFont(new Font("Tahoma", Font.BOLD, 12));
	    test_desc_lb.setBounds(1115, 96, 155, 22);
	    contentPane.add(test_desc_lb);
	    
	    test_desc_tp = new JTextPane();
	    test_desc_tp.setBackground(new Color(245, 255, 250));
	    test_desc_tp.setBounds(1115, 123, 155, 166);
	    contentPane.add(test_desc_tp);
	    
	    s_precision_tx = new JTextField();
	    s_precision_tx.setBackground(SystemColor.text);
	    s_precision_tx.setToolTipText("Spatial precision.");
	    s_precision_tx.setText("0.0000001");
	    s_precision_tx.setBounds(10, 436, 65, 20);
	    contentPane.add(s_precision_tx);
	    s_precision_tx.setColumns(10);
	    
	    n_dec_dig_tx = new JTextField();
	    n_dec_dig_tx.setBackground(new Color(245, 255, 250));
	    n_dec_dig_tx.setToolTipText("Number of decimal  digits.");
	    n_dec_dig_tx.setText("2");
	    n_dec_dig_tx.setBounds(100, 436, 65, 20);
	    contentPane.add(n_dec_dig_tx);
	    n_dec_dig_tx.setColumns(10);
	    
	    op_cb = new JComboBox<>();
	    op_cb.setModel(new DefaultComboBoxModel(new String[] {"Intersects", "Touches (Meets)", "Equals", "Disjoint", "Contains", "Within (Inside)", "Overlaps", "CoveredBy", "Covers"}));
	    op_cb.setSelectedIndex(0);
	    op_cb.setBounds(10, 106, 155, 20);
	    contentPane.add(op_cb);
	    
	    P2 = new JTextArea();
	    P2.setText("POLYGON((879.41392092742944442 729.71448703117766854, 889.59586843560805391 719.23611292160808262, 905.30234479740443021 716.51898401674543493, 915.69536819172503783 720.30301183894971473, 919.65333894372611212 729.96845561698000893, 914.43391940942797191 734.93882689411861975, 913.08115780326852473 743.50976093106328335, 907.10894991356440187 745.86812153907453649, 903.46665239345543341 752.06605014146452959, 894.28654149784210858 754.96664410872506323, 886.51609268522088314 753.56158382969033482, 874.69227938276412715 747.81969845663002161, 865.6532279740820286 749.37989383540730159, 862.54327071581406017 752.79927334168314701, 858.65736615717491986 753.99565981920409286, 855.74808947198516762 752.74425405949409651, 855.01914955103779903 748.80008871936524883, 855.73428406011316838 742.3498703605157516, 863.61937324107020686 733.62936271821831724, 879.41392092742944442 729.71448703117766854))");
	    P2.setToolTipText("Moving segment data.");
	    P2.setBackground(SystemColor.controlLtHighlight);
	    P2.setBounds(10, 238, 155, 36);
	    contentPane.add(P2);
	    
	    Q2 = new JTextArea();
	    Q2.setText("POLYGON((892.35306594597261665 747.89388402949066403, 917.06000986635353911 752.5446028850917628, 931.30283636163187566 760.68336088239379933, 938.47797773822651379 772.87467253697695924, 936.18453215883982921 779.75047079443834264, 921.71072872195463788 782.19293558954893797, 917.35067979482857936 789.75035372990066662, 913.00028657183486303 794.88279196285293438, 908.33555012343322232 791.53755352151483748, 901.45521338527396438 794.81174316792498757, 890.64325565388071482 785.64401215797647637, 880.48656808802650175 774.51176736018214797, 873.27859626709800978 769.92790185520789237, 865.9021024547412253 767.95010909427048773, 860.08870388523973816 772.6008279498715865, 856.01932488658871989 777.83288666242287945, 853.98463538726332445 774.92618737767213588, 855.72865495811367964 768.24077902274552798, 864.44875281236579667 755.45130216984250637, 892.35306594597261665 747.89388402949066403))");
	    Q2.setToolTipText("Moving point data.");
	    Q2.setBackground(new Color(230, 230, 250));
	    Q2.setBounds(10, 277, 155, 36);
	    contentPane.add(Q2);
	    
	    i1 = new JButton("Test I");
	    i1.setForeground(new Color(0, 0, 128));
	    i1.setFont(new Font("Tahoma", Font.BOLD, 11));
	    i1.setBounds(1111, 372, 155, 23);
	    contentPane.add(i1);
	    
	    i2 = new JButton("Test II");
	    i2.setForeground(new Color(0, 0, 128));
	    i2.setFont(new Font("Tahoma", Font.BOLD, 11));
	    i2.setBounds(1111, 397, 155, 23);
	    contentPane.add(i2);
	    
	    i3 = new JButton("Test III");
	    i3.setForeground(new Color(0, 0, 128));
	    i3.setFont(new Font("Tahoma", Font.BOLD, 11));
	    i3.setBounds(1111, 422, 155, 23);
	    contentPane.add(i3);
	    
	    i4 = new JButton("Test IV");
	    i4.setForeground(new Color(0, 0, 128));
	    i4.setFont(new Font("Tahoma", Font.BOLD, 11));
	    i4.setBounds(1110, 447, 155, 23);
	    contentPane.add(i4);
	    
	    i5 = new JButton("Test V");
	    i5.setForeground(new Color(0, 0, 128));
	    i5.setFont(new Font("Tahoma", Font.BOLD, 11));
	    i5.setBounds(1111, 472, 155, 23);
	    contentPane.add(i5);
	    
	    i6 = new JButton("Test VI");
	    i6.setForeground(new Color(0, 0, 128));
	    i6.setFont(new Font("Tahoma", Font.BOLD, 11));
	    i6.setBounds(1111, 497, 155, 23);
	    contentPane.add(i6);
	    
	    leg_bt = new JButton("Show Legend");
	    leg_bt.setForeground(new Color(0, 0, 128));
	    leg_bt.setFont(new Font("Tahoma", Font.BOLD, 11));
	    leg_bt.setBounds(10, 554, 155, 23);
	    contentPane.add(leg_bt);
	    
		btn_Intersects = new JButton("Intersects");
		btn_Intersects.setForeground(new Color(0, 0, 128));
		btn_Intersects.setFont(new Font("Tahoma", Font.BOLD, 11));
		btn_Intersects.setBounds(8, 523, 155, 23);
		contentPane.add(btn_Intersects);
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
        
        // ID
    	i1.addActionListener(new ActionListener() 
    	{
			public void actionPerformed(ActionEvent arg0) 
			{
				DrawGraphs c = (DrawGraphs) jp;

				p1.setText("POLYGON((975.0420063220051 697.090167065809, 968.2376237623762 719.366754617414, 949.8141049487542 719.682075626039, 947.5206593693675 726.5578738835004, 929.1730947342762 738.0175376459358, 929.5007298170459 743.256241080192, 924.3364137823626 741.690195051915, 919.6716773339609 738.3449566105769, 912.7913405958017 741.619146256987, 901.9793828644084 732.4514152470385, 891.8226952985542 721.3191704492442, 884.6147234776257 716.73530494427, 877.4067516566968 712.1514394392957, 873.1474955806933 721.3191704492442, 868.8882395046899 730.4869014591925, 851.6435643564355 749.7625329815303, 845.7678029771724 751.5623397481193, 839.0734469726663 758.972351382961, 829.2443944895814 769.7771772161138, 823.6745980825001 760.609446206166, 814 751.4999999999998, 811.0891089108911 744.6965699208442, 802.3783177024834 736.3804428227309, 798 736, 769.3716535620496 707.0652770818208, 757.5275973847811 695.0944675046978, 734.5578555691986 671.8789067884509, 719.8142768445714 645.3579706525286, 721.7800873411885 635.8628206779392, 723.7458978378055 621.1289672690934, 735.4026288700353 597.7088326122334, 738 589, 763.0621077701443 576.5999880779154, 814 568, 845.6261486280558 565.4677432801209, 852 570, 878.7172919877744 575.2903122193516, 892.7049504950495 586.1319261213721, 901.829702970297 592.211081794195, 907.3811614420508 597.0972549398289, 928 614.0000000000002, 975.0420063220051 697.090167065809))");
				q1.setText("POLYGON((965 635, 963.1683168316831 648.4432717678101, 958.0990099009902 658.5751978891822, 947.960396039604 658.5751978891822, 942 675, 932 679, 933.5 683.9999999999998, 935 689, 919.2997169901681 692.9781016562131, 907.4059405940594 688.9709762532982, 897.2673267326733 683.9050131926122, 884.6074998412831 681.6848638401293, 875 680, 875.5385318320745 694.8658276536648, 871 710, 861.6493140294922 728.7013719410154, 858.3483767115072 735.028033248251, 855.0474393935223 741.3546945554867, 851.6115528967149 747.7221555823205, 837.1294340674169 742.0589775899646, 826.2970297029703 734.5646437994724, 816.1584158415842 729.4986807387863, 810.6838257704394 731.3618636044034, 793.0534202391211 721.608612617568, 772.9043853461864 709.6530146337057, 755.3267326732673 704.1688654353561, 741 698, 724.9108910891089 688.9709762532982, 704.6336633663364 668.707124010554, 703 651.0000000000002, 702.6975918911147 637.9194267305304, 705 626, 714.7722772277225 602.8496042216359, 760 570, 795.8811881188119 552.1899736147757, 834.2959760355977 574.0513638167383, 846.5742574257424 562.3218997361478, 878 573.0000000000002, 887.1287128712871 572.4538258575199, 902.3366336633663 582.5857519788917, 950.7825840103793 618.7275457564351, 965 635))");

				P2.setText("POLYGON((879.41392092742944442 729.71448703117766854, 889.59586843560805391 719.23611292160808262, 905.30234479740443021 716.51898401674543493, 915.69536819172503783 720.30301183894971473, 919.65333894372611212 729.96845561698000893, 914.43391940942797191 734.93882689411861975, 913.08115780326852473 743.50976093106328335, 907.10894991356440187 745.86812153907453649, 903.46665239345543341 752.06605014146452959, 894.28654149784210858 754.96664410872506323, 886.51609268522088314 753.56158382969033482, 874.69227938276412715 747.81969845663002161, 865.6532279740820286 749.37989383540730159, 862.54327071581406017 752.79927334168314701, 858.65736615717491986 753.99565981920409286, 855.74808947198516762 752.74425405949409651, 855.01914955103779903 748.80008871936524883, 855.73428406011316838 742.3498703605157516, 863.61937324107020686 733.62936271821831724, 879.41392092742944442 729.71448703117766854))");
				Q2.setText("POLYGON((892.35306594597261665 747.89388402949066403, 917.06000986635353911 752.5446028850917628, 931.30283636163187566 760.68336088239379933, 938.47797773822651379 772.87467253697695924, 936.18453215883982921 779.75047079443834264, 921.71072872195463788 782.19293558954893797, 917.35067979482857936 789.75035372990066662, 913.00028657183486303 794.88279196285293438, 908.33555012343322232 791.53755352151483748, 901.45521338527396438 794.81174316792498757, 890.64325565388071482 785.64401215797647637, 880.48656808802650175 774.51176736018214797, 873.27859626709800978 769.92790185520789237, 865.9021024547412253 767.95010909427048773, 860.08870388523973816 772.6008279498715865, 856.01932488658871989 777.83288666242287945, 853.98463538726332445 774.92618737767213588, 855.72865495811367964 768.24077902274552798, 864.44875281236579667 755.45130216984250637, 892.35306594597261665 747.89388402949066403))");

				test_desc_tp.setText("MR A and MR B initially intersect and become disjoint.");
	            jp.repaint();
			}
		});
    	
    	leg_bt.addActionListener(new ActionListener() 
    	{
			public void actionPerformed(ActionEvent arg0) 
			{
				DrawGraphs c = (DrawGraphs) jp;

				if(show_leg)
					show_leg = false;
				else
					show_leg = true;

	            jp.repaint();
			}
		});
    	
        // ID
    	i6.addActionListener(new ActionListener() 
    	{
			public void actionPerformed(ActionEvent arg0) 
			{
				DrawGraphs c = (DrawGraphs) jp;

				p1.setText("POLYGON((975.0420063220051 697.090167065809, 968.2376237623762 719.366754617414, 949.8141049487542 719.682075626039, 947.5206593693675 726.5578738835004, 929.1730947342762 738.0175376459358, 929.5007298170459 743.256241080192, 924.3364137823626 741.690195051915, 919.6716773339609 738.3449566105769, 912.7913405958017 741.619146256987, 901.9793828644084 732.4514152470385, 891.8226952985542 721.3191704492442, 884.6147234776257 716.73530494427, 877.4067516566968 712.1514394392957, 873.1474955806933 721.3191704492442, 868.8882395046899 730.4869014591925, 851.6435643564355 749.7625329815303, 845.7678029771724 751.5623397481193, 839.0734469726663 758.972351382961, 829.2443944895814 769.7771772161138, 823.6745980825001 760.609446206166, 814 751.4999999999998, 811.0891089108911 744.6965699208442, 802.3783177024834 736.3804428227309, 798 736, 769.3716535620496 707.0652770818208, 757.5275973847811 695.0944675046978, 734.5578555691986 671.8789067884509, 719.8142768445714 645.3579706525286, 721.7800873411885 635.8628206779392, 723.7458978378055 621.1289672690934, 735.4026288700353 597.7088326122334, 738 589, 763.0621077701443 576.5999880779154, 814 568, 845.6261486280558 565.4677432801209, 852 570, 878.7172919877744 575.2903122193516, 892.7049504950495 586.1319261213721, 901.829702970297 592.211081794195, 907.3811614420508 597.0972549398289, 928 614.0000000000002, 975.0420063220051 697.090167065809))");
				q1.setText("POLYGON((965 635, 963.1683168316831 648.4432717678101, 958.0990099009902 658.5751978891822, 947.960396039604 658.5751978891822, 942 675, 932 679, 933.5 683.9999999999998, 935 689, 919.2997169901681 692.9781016562131, 907.4059405940594 688.9709762532982, 897.2673267326733 683.9050131926122, 884.6074998412831 681.6848638401293, 875 680, 875.5385318320745 694.8658276536648, 871 710, 861.6493140294922 728.7013719410154, 858.3483767115072 735.028033248251, 855.0474393935223 741.3546945554867, 851.6115528967149 747.7221555823205, 837.1294340674169 742.0589775899646, 826.2970297029703 734.5646437994724, 816.1584158415842 729.4986807387863, 810.6838257704394 731.3618636044034, 793.0534202391211 721.608612617568, 772.9043853461864 709.6530146337057, 755.3267326732673 704.1688654353561, 741 698, 724.9108910891089 688.9709762532982, 704.6336633663364 668.707124010554, 703 651.0000000000002, 702.6975918911147 637.9194267305304, 705 626, 714.7722772277225 602.8496042216359, 760 570, 795.8811881188119 552.1899736147757, 834.2959760355977 574.0513638167383, 846.5742574257424 562.3218997361478, 878 573.0000000000002, 887.1287128712871 572.4538258575199, 902.3366336633663 582.5857519788917, 950.7825840103793 618.7275457564351, 965 635))");

				P2.setText("Polygon ((748.80098648344142021 733.46200304065894215, 760.84418475839777329 725.18977514549726493, 776.77832191718437116 725.61340492996339435, 786.22463162522683433 731.36675480059125221, 788.20523617735966582 741.62168247015733868, 782.11054426960947694 745.46897521405162479, 779.09922089530255107 753.60671481200563449, 772.77992586063794533 754.74497756731545905, 767.99025418557687317 760.10591922251308006, 758.41905820139072603 761.1451924546150849, 751.07646438292408675 758.23995835831522072, 740.61218070717939099 750.28567801360395606, 731.44280049178235004 750.03844036630630399, 727.72131581929954791 752.77970689633741586, 723.67604402899030447 753.1888168876311056, 721.06955344101311312 751.38989665004146445, 721.13022164038488881 747.3793963061679051, 723.09944923275418205 741.19563717984669893, 732.54503161323282256 734.1954330096382364, 748.80098648344142021 733.46200304065894215))");
				Q2.setText("Polygon ((958.96950724370094576 591.32745931417821339, 973.11009655979603394 570.4387693834488573, 985.778314790770537 560.01697802276305538, 996.86654358164435052 559.38213668256196343, 1003.35323895748501855 565.86883205840263145, 1001.44538737635537018 574.0725938572600171, 1005.8686271803173895 581.96778186931248911, 1007.27439169793888141 588.05942811233887824, 1006.45900714589788549 592.44823461685598431, 1000.49146158579060284 597.72995346326729305, 996.60099443451656498 608.88556911413843409, 986.7549302016573165 615.09140285154671801, 977.97881292846113865 615.66375832588562389, 971.11054723639449549 618.33475053946710887, 968.63034018092594124 623.4859498085170344, 965.5777776511185948 625.39380138964668276, 962.14364480508527322 624.05830528285594028, 961.38050417263343661 619.86103180437078208, 958.36668505313252808 615.7586434986490076, 958.96950724370094576 591.32745931417821339))");

				test_desc_tp.setText("The two MRs are initially disjoint. They intersect and MR B stays inside MR A during a period of time. Then, the two MRs become disjoint again.");
	            jp.repaint();
			}
		});    	
    	
    	// DInside
    	i5.addActionListener(new ActionListener() 
    	{
			public void actionPerformed(ActionEvent arg0) 
			{
				DrawGraphs c = (DrawGraphs) jp;

				p1.setText("POLYGON((975.0420063220051 697.090167065809, 968.2376237623762 719.366754617414, 949.8141049487542 719.682075626039, 947.5206593693675 726.5578738835004, 929.1730947342762 738.0175376459358, 929.5007298170459 743.256241080192, 924.3364137823626 741.690195051915, 919.6716773339609 738.3449566105769, 912.7913405958017 741.619146256987, 901.9793828644084 732.4514152470385, 891.8226952985542 721.3191704492442, 884.6147234776257 716.73530494427, 877.4067516566968 712.1514394392957, 873.1474955806933 721.3191704492442, 868.8882395046899 730.4869014591925, 851.6435643564355 749.7625329815303, 845.7678029771724 751.5623397481193, 839.0734469726663 758.972351382961, 829.2443944895814 769.7771772161138, 823.6745980825001 760.609446206166, 814 751.4999999999998, 811.0891089108911 744.6965699208442, 802.3783177024834 736.3804428227309, 798 736, 769.3716535620496 707.0652770818208, 757.5275973847811 695.0944675046978, 734.5578555691986 671.8789067884509, 719.8142768445714 645.3579706525286, 721.7800873411885 635.8628206779392, 723.7458978378055 621.1289672690934, 735.4026288700353 597.7088326122334, 738 589, 763.0621077701443 576.5999880779154, 814 568, 845.6261486280558 565.4677432801209, 852 570, 878.7172919877744 575.2903122193516, 892.7049504950495 586.1319261213721, 901.829702970297 592.211081794195, 907.3811614420508 597.0972549398289, 928 614.0000000000002, 975.0420063220051 697.090167065809))");
				q1.setText("POLYGON((965 635, 963.1683168316831 648.4432717678101, 958.0990099009902 658.5751978891822, 947.960396039604 658.5751978891822, 942 675, 932 679, 933.5 683.9999999999998, 935 689, 919.2997169901681 692.9781016562131, 907.4059405940594 688.9709762532982, 897.2673267326733 683.9050131926122, 884.6074998412831 681.6848638401293, 875 680, 875.5385318320745 694.8658276536648, 871 710, 861.6493140294922 728.7013719410154, 858.3483767115072 735.028033248251, 855.0474393935223 741.3546945554867, 851.6115528967149 747.7221555823205, 837.1294340674169 742.0589775899646, 826.2970297029703 734.5646437994724, 816.1584158415842 729.4986807387863, 810.6838257704394 731.3618636044034, 793.0534202391211 721.608612617568, 772.9043853461864 709.6530146337057, 755.3267326732673 704.1688654353561, 741 698, 724.9108910891089 688.9709762532982, 704.6336633663364 668.707124010554, 703 651.0000000000002, 702.6975918911147 637.9194267305304, 705 626, 714.7722772277225 602.8496042216359, 760 570, 795.8811881188119 552.1899736147757, 834.2959760355977 574.0513638167383, 846.5742574257424 562.3218997361478, 878 573.0000000000002, 887.1287128712871 572.4538258575199, 902.3366336633663 582.5857519788917, 950.7825840103793 618.7275457564351, 965 635))");

				Q2.setText("Polygon ((748.80098648344142021 733.46200304065894215, 760.84418475839777329 725.18977514549726493, 776.77832191718437116 725.61340492996339435, 786.22463162522683433 731.36675480059125221, 788.20523617735966582 741.62168247015733868, 782.11054426960947694 745.46897521405162479, 779.09922089530255107 753.60671481200563449, 772.77992586063794533 754.74497756731545905, 767.99025418557687317 760.10591922251308006, 758.41905820139072603 761.1451924546150849, 751.07646438292408675 758.23995835831522072, 740.61218070717939099 750.28567801360395606, 731.44280049178235004 750.03844036630630399, 727.72131581929954791 752.77970689633741586, 723.67604402899030447 753.1888168876311056, 721.06955344101311312 751.38989665004146445, 721.13022164038488881 747.3793963061679051, 723.09944923275418205 741.19563717984669893, 732.54503161323282256 734.1954330096382364, 748.80098648344142021 733.46200304065894215))");
				P2.setText("Polygon ((815.49906834275384426 667.0691670850239916, 829.63965765884893244 646.18047715429463551, 842.3078758898234355 635.75868579360883359, 853.39610468069724902 635.12384445340774164, 859.88280005653791704 641.61053982924840966, 857.97494847540826868 649.81430162810579532, 862.398188279370288 657.70948964015826732, 863.80395279699177991 663.80113588318465645, 862.98856824495078399 668.18994238770176253, 857.02102268484350134 673.47166123411307126, 853.13055553356946348 684.6272768849842123, 843.284491300710215 690.83311062239249623, 834.50837402751403715 691.4054660967314021, 827.64010833544739398 694.07645831031288708, 825.15990127997883974 699.22765757936281261, 822.1073387501714933 701.13550916049246098, 818.67320590413817172 699.80001305370171849, 817.91006527168633511 695.6027395752165603, 814.89624615218542658 691.50035126949478581, 815.49906834275384426 667.0691670850239916))");

				test_desc_tp.setText("The two MRs are initially disjoint. Then, they intersect and MR B stays inside MR A.");
	            jp.repaint();
			}
		});    	
    	
    	// D
    	i4.addActionListener(new ActionListener() 
    	{
			public void actionPerformed(ActionEvent arg0) 
			{
				DrawGraphs c = (DrawGraphs) jp;

				p1.setText("POLYGON((975.0420063220051 697.090167065809, 968.2376237623762 719.366754617414, 949.8141049487542 719.682075626039, 947.5206593693675 726.5578738835004, 929.1730947342762 738.0175376459358, 929.5007298170459 743.256241080192, 924.3364137823626 741.690195051915, 919.6716773339609 738.3449566105769, 912.7913405958017 741.619146256987, 901.9793828644084 732.4514152470385, 891.8226952985542 721.3191704492442, 884.6147234776257 716.73530494427, 877.4067516566968 712.1514394392957, 873.1474955806933 721.3191704492442, 868.8882395046899 730.4869014591925, 851.6435643564355 749.7625329815303, 845.7678029771724 751.5623397481193, 839.0734469726663 758.972351382961, 829.2443944895814 769.7771772161138, 823.6745980825001 760.609446206166, 814 751.4999999999998, 811.0891089108911 744.6965699208442, 802.3783177024834 736.3804428227309, 798 736, 769.3716535620496 707.0652770818208, 757.5275973847811 695.0944675046978, 734.5578555691986 671.8789067884509, 719.8142768445714 645.3579706525286, 721.7800873411885 635.8628206779392, 723.7458978378055 621.1289672690934, 735.4026288700353 597.7088326122334, 738 589, 763.0621077701443 576.5999880779154, 814 568, 845.6261486280558 565.4677432801209, 852 570, 878.7172919877744 575.2903122193516, 892.7049504950495 586.1319261213721, 901.829702970297 592.211081794195, 907.3811614420508 597.0972549398289, 928 614.0000000000002, 975.0420063220051 697.090167065809))");
				q1.setText("POLYGON((965 635, 963.1683168316831 648.4432717678101, 958.0990099009902 658.5751978891822, 947.960396039604 658.5751978891822, 942 675, 932 679, 933.5 683.9999999999998, 935 689, 919.2997169901681 692.9781016562131, 907.4059405940594 688.9709762532982, 897.2673267326733 683.9050131926122, 884.6074998412831 681.6848638401293, 875 680, 875.5385318320745 694.8658276536648, 871 710, 861.6493140294922 728.7013719410154, 858.3483767115072 735.028033248251, 855.0474393935223 741.3546945554867, 851.6115528967149 747.7221555823205, 837.1294340674169 742.0589775899646, 826.2970297029703 734.5646437994724, 816.1584158415842 729.4986807387863, 810.6838257704394 731.3618636044034, 793.0534202391211 721.608612617568, 772.9043853461864 709.6530146337057, 755.3267326732673 704.1688654353561, 741 698, 724.9108910891089 688.9709762532982, 704.6336633663364 668.707124010554, 703 651.0000000000002, 702.6975918911147 637.9194267305304, 705 626, 714.7722772277225 602.8496042216359, 760 570, 795.8811881188119 552.1899736147757, 834.2959760355977 574.0513638167383, 846.5742574257424 562.3218997361478, 878 573.0000000000002, 887.1287128712871 572.4538258575199, 902.3366336633663 582.5857519788917, 950.7825840103793 618.7275457564351, 965 635))");

				Q2.setText("POLYGON((879.41392092742944442 729.71448703117766854, 889.59586843560805391 719.23611292160808262, 905.30234479740443021 716.51898401674543493, 915.69536819172503783 720.30301183894971473, 919.65333894372611212 729.96845561698000893, 914.43391940942797191 734.93882689411861975, 913.08115780326852473 743.50976093106328335, 907.10894991356440187 745.86812153907453649, 903.46665239345543341 752.06605014146452959, 894.28654149784210858 754.96664410872506323, 886.51609268522088314 753.56158382969033482, 874.69227938276412715 747.81969845663002161, 865.6532279740820286 749.37989383540730159, 862.54327071581406017 752.79927334168314701, 858.65736615717491986 753.99565981920409286, 855.74808947198516762 752.74425405949409651, 855.01914955103779903 748.80008871936524883, 855.73428406011316838 742.3498703605157516, 863.61937324107020686 733.62936271821831724, 879.41392092742944442 729.71448703117766854))");
				P2.setText("POLYGON((892.35306594597261665 747.89388402949066403, 917.06000986635353911 752.5446028850917628, 931.30283636163187566 760.68336088239379933, 938.47797773822651379 772.87467253697695924, 936.18453215883982921 779.75047079443834264, 921.71072872195463788 782.19293558954893797, 917.35067979482857936 789.75035372990066662, 913.00028657183486303 794.88279196285293438, 908.33555012343322232 791.53755352151483748, 901.45521338527396438 794.81174316792498757, 890.64325565388071482 785.64401215797647637, 880.48656808802650175 774.51176736018214797, 873.27859626709800978 769.92790185520789237, 865.9021024547412253 767.95010909427048773, 860.08870388523973816 772.6008279498715865, 856.01932488658871989 777.83288666242287945, 853.98463538726332445 774.92618737767213588, 855.72865495811367964 768.24077902274552798, 864.44875281236579667 755.45130216984250637, 892.35306594597261665 747.89388402949066403))");

				test_desc_tp.setText("The two MRs are disjoint during their evolution.");
	            jp.repaint();
			}
		});    	
        
    	// DI
    	i3.addActionListener(new ActionListener() 
    	{
			public void actionPerformed(ActionEvent arg0) 
			{
				DrawGraphs c = (DrawGraphs) jp;

				p1.setText("POLYGON((975.0420063220051 697.090167065809, 968.2376237623762 719.366754617414, 949.8141049487542 719.682075626039, 947.5206593693675 726.5578738835004, 929.1730947342762 738.0175376459358, 929.5007298170459 743.256241080192, 924.3364137823626 741.690195051915, 919.6716773339609 738.3449566105769, 912.7913405958017 741.619146256987, 901.9793828644084 732.4514152470385, 891.8226952985542 721.3191704492442, 884.6147234776257 716.73530494427, 877.4067516566968 712.1514394392957, 873.1474955806933 721.3191704492442, 868.8882395046899 730.4869014591925, 851.6435643564355 749.7625329815303, 845.7678029771724 751.5623397481193, 839.0734469726663 758.972351382961, 829.2443944895814 769.7771772161138, 823.6745980825001 760.609446206166, 814 751.4999999999998, 811.0891089108911 744.6965699208442, 802.3783177024834 736.3804428227309, 798 736, 769.3716535620496 707.0652770818208, 757.5275973847811 695.0944675046978, 734.5578555691986 671.8789067884509, 719.8142768445714 645.3579706525286, 721.7800873411885 635.8628206779392, 723.7458978378055 621.1289672690934, 735.4026288700353 597.7088326122334, 738 589, 763.0621077701443 576.5999880779154, 814 568, 845.6261486280558 565.4677432801209, 852 570, 878.7172919877744 575.2903122193516, 892.7049504950495 586.1319261213721, 901.829702970297 592.211081794195, 907.3811614420508 597.0972549398289, 928 614.0000000000002, 975.0420063220051 697.090167065809))");
				q1.setText("POLYGON((965 635, 963.1683168316831 648.4432717678101, 958.0990099009902 658.5751978891822, 947.960396039604 658.5751978891822, 942 675, 932 679, 933.5 683.9999999999998, 935 689, 919.2997169901681 692.9781016562131, 907.4059405940594 688.9709762532982, 897.2673267326733 683.9050131926122, 884.6074998412831 681.6848638401293, 875 680, 875.5385318320745 694.8658276536648, 871 710, 861.6493140294922 728.7013719410154, 858.3483767115072 735.028033248251, 855.0474393935223 741.3546945554867, 851.6115528967149 747.7221555823205, 837.1294340674169 742.0589775899646, 826.2970297029703 734.5646437994724, 816.1584158415842 729.4986807387863, 810.6838257704394 731.3618636044034, 793.0534202391211 721.608612617568, 772.9043853461864 709.6530146337057, 755.3267326732673 704.1688654353561, 741 698, 724.9108910891089 688.9709762532982, 704.6336633663364 668.707124010554, 703 651.0000000000002, 702.6975918911147 637.9194267305304, 705 626, 714.7722772277225 602.8496042216359, 760 570, 795.8811881188119 552.1899736147757, 834.2959760355977 574.0513638167383, 846.5742574257424 562.3218997361478, 878 573.0000000000002, 887.1287128712871 572.4538258575199, 902.3366336633663 582.5857519788917, 950.7825840103793 618.7275457564351, 965 635))");

				//P2.setText("POLYGON((886.44731774168656102 757.91150527461786623, 909.26338260372608602 739.69886313920324028, 925.05273749538832817 735.24984522303384438, 938.77619961922459879 738.68165538225377986, 940.91425559995741423 748.02316238963419437, 933.29536845906829967 755.31784156708113187, 935.2406162397207936 763.09883268969133496, 931.83643262357895765 768.93457603164893044, 930.9491141599698949 773.25918858474835815, 925.35227335473712174 778.98502289835369083, 914.34208026896567389 781.74196753649096081, 899.28326833834898935 781.17862058591902041, 890.96106103256079223 783.10411955981658139, 884.37888209908237513 786.97700551948855718, 883.6189270840015979 794.38289892790191971, 882.39471819866037094 798.43750070487897119, 879.47684652768157321 798.59960468660005972, 877.45310430740414631 794.43469450162319845, 876.07266291153950988 780.03869877954036838, 886.44731774168656102 757.91150527461786623))");
				P2.setText("POLYGON((863.92774772258860594 778.90792457994507458, 883.6793596655750207 757.41032064380488009, 898.59916909986770861 750.59146628565588344, 912.68667752100373036 751.87709458252538752, 916.23265800082822352 760.77996260257316408, 909.82317907649473909 769.15721546290922106, 912.93920898539022346 776.54762610002137535, 910.47069134980552008 782.83656775410099726, 910.25739094108121208 787.24611543225637433, 905.60531419103767803 793.76286212809191056, 895.14847156366045056 798.17642506408697045, 880.18152350634431969 799.93017601504925551, 872.25327469167757499 803.10972810170108005, 866.34323397773414399 807.94664281342397771, 866.7285406145658726 815.38144796200322162, 866.14091163525449701 819.57586987062018125, 863.28245871744229589 820.18373474527629696, 860.64366808099464379 816.37863377420421784, 857.07083713935867308 802.36488372861913376, 863.92774772258860594 778.90792457994507458))");
				Q2.setText("POLYGON((867.13689313980376028 692.93600761039795088, 879.18009141476011337 684.66377971523627366, 895.11422857354671123 685.08740949970240308, 904.5605382815891744 690.84075937033026094, 906.54114283372200589 701.09568703989634741, 900.44645092597181701 704.94297978379063352, 897.43512755166489114 713.08071938174464321, 891.11583251700028541 714.21898213705446778, 886.32616084193921324 719.57992379225208879, 876.7549648577530661 720.61919702435409363, 869.41237103928642682 717.71396292805422945, 858.94808736354173107 709.75968258334296479, 849.77870714814469011 709.51244493604531272, 846.05722247566188798 712.25371146607642459, 842.01195068535264454 712.66282145737011433, 839.40546009737545319 710.86390121978047318, 839.46612829674722889 706.85340087590691383, 841.43535588911652212 700.66964174958570766, 850.88093826959516264 693.66943757937724513, 867.13689313980376028 692.93600761039795088))");

				test_desc_tp.setText("MR A and MR B are initially disjoint and then intersect. The regions intersect, but none contains the other.");
	            jp.repaint();
			}
		});   
    	
    	// DID
    	i2.addActionListener(new ActionListener() 
    	{
			public void actionPerformed(ActionEvent arg0) 
			{
				DrawGraphs c = (DrawGraphs) jp;

				p1.setText("POLYGON((975.0420063220051 697.090167065809, 968.2376237623762 719.366754617414, 949.8141049487542 719.682075626039, 947.5206593693675 726.5578738835004, 929.1730947342762 738.0175376459358, 929.5007298170459 743.256241080192, 924.3364137823626 741.690195051915, 919.6716773339609 738.3449566105769, 912.7913405958017 741.619146256987, 901.9793828644084 732.4514152470385, 891.8226952985542 721.3191704492442, 884.6147234776257 716.73530494427, 877.4067516566968 712.1514394392957, 873.1474955806933 721.3191704492442, 868.8882395046899 730.4869014591925, 851.6435643564355 749.7625329815303, 845.7678029771724 751.5623397481193, 839.0734469726663 758.972351382961, 829.2443944895814 769.7771772161138, 823.6745980825001 760.609446206166, 814 751.4999999999998, 811.0891089108911 744.6965699208442, 802.3783177024834 736.3804428227309, 798 736, 769.3716535620496 707.0652770818208, 757.5275973847811 695.0944675046978, 734.5578555691986 671.8789067884509, 719.8142768445714 645.3579706525286, 721.7800873411885 635.8628206779392, 723.7458978378055 621.1289672690934, 735.4026288700353 597.7088326122334, 738 589, 763.0621077701443 576.5999880779154, 814 568, 845.6261486280558 565.4677432801209, 852 570, 878.7172919877744 575.2903122193516, 892.7049504950495 586.1319261213721, 901.829702970297 592.211081794195, 907.3811614420508 597.0972549398289, 928 614.0000000000002, 975.0420063220051 697.090167065809))");
				q1.setText("POLYGON((965 635, 963.1683168316831 648.4432717678101, 958.0990099009902 658.5751978891822, 947.960396039604 658.5751978891822, 942 675, 932 679, 933.5 683.9999999999998, 935 689, 919.2997169901681 692.9781016562131, 907.4059405940594 688.9709762532982, 897.2673267326733 683.9050131926122, 884.6074998412831 681.6848638401293, 875 680, 875.5385318320745 694.8658276536648, 871 710, 861.6493140294922 728.7013719410154, 858.3483767115072 735.028033248251, 855.0474393935223 741.3546945554867, 851.6115528967149 747.7221555823205, 837.1294340674169 742.0589775899646, 826.2970297029703 734.5646437994724, 816.1584158415842 729.4986807387863, 810.6838257704394 731.3618636044034, 793.0534202391211 721.608612617568, 772.9043853461864 709.6530146337057, 755.3267326732673 704.1688654353561, 741 698, 724.9108910891089 688.9709762532982, 704.6336633663364 668.707124010554, 703 651.0000000000002, 702.6975918911147 637.9194267305304, 705 626, 714.7722772277225 602.8496042216359, 760 570, 795.8811881188119 552.1899736147757, 834.2959760355977 574.0513638167383, 846.5742574257424 562.3218997361478, 878 573.0000000000002, 887.1287128712871 572.4538258575199, 902.3366336633663 582.5857519788917, 950.7825840103793 618.7275457564351, 965 635))");

				P2.setText("Polygon ((748.80098648344142021 733.46200304065894215, 760.84418475839777329 725.18977514549726493, 776.77832191718437116 725.61340492996339435, 786.22463162522683433 731.36675480059125221, 788.20523617735966582 741.62168247015733868, 782.11054426960947694 745.46897521405162479, 779.09922089530255107 753.60671481200563449, 772.77992586063794533 754.74497756731545905, 767.99025418557687317 760.10591922251308006, 758.41905820139072603 761.1451924546150849, 751.07646438292408675 758.23995835831522072, 740.61218070717939099 750.28567801360395606, 731.44280049178235004 750.03844036630630399, 727.72131581929954791 752.77970689633741586, 723.67604402899030447 753.1888168876311056, 721.06955344101311312 751.38989665004146445, 721.13022164038488881 747.3793963061679051, 723.09944923275418205 741.19563717984669893, 732.54503161323282256 734.1954330096382364, 748.80098648344142021 733.46200304065894215))");
				//Q2.setText("Polygon ((909.965278531365243 715.03895578185358772, 929.71689047435165776 693.54135184571339323, 944.63669990864434567 686.72249748756439658, 958.72420832978036742 688.00812578443390066, 962.27018880960486058 696.91099380448167722, 955.86070988527137615 705.2882466648177342, 958.97673979416686052 712.67865730192988849, 956.50822215858215714 718.9675989560095104, 956.29492174985784914 723.37714663416488747, 951.64284499981431509 729.8938933300004237, 941.18600237243708762 734.30745626599548359, 926.21905431512095674 736.06120721695776865, 918.29080550045421205 739.24075930360959319, 912.38076478651078105 744.07767401533249085, 912.76607142334250966 751.51247916391173476, 912.17844244403113407 755.70690107252869439, 909.31998952621893295 756.3147659471848101, 906.68119888977128085 752.50966497611273098, 903.10836794813531014 738.4959149305276469, 909.965278531365243 715.03895578185358772))");
				//Q2.setText("Polygon ((909.965278531365243 715.03895578185358772, 929.71689047435165776 693.54135184571339323, 944.63669990864434567 686.72249748756439658, 958.72420832978036742 688.00812578443390066, 962.27018880960486058 696.91099380448167722, 961.36501918763156027 705.25394131767916406, 958.97673979416686052 712.67865730192988849, 956.50822215858215714 718.9675989560095104, 956.29492174985784914 723.37714663416488747, 951.64284499981431509 729.8938933300004237, 941.18600237243708762 734.30745626599548359, 926.21905431512095674 736.06120721695776865, 918.29080550045421205 739.24075930360959319, 913.68078667082215816 744.45687479177138357, 910.76291499984336042 746.32107058156339008, 907.84504332886456268 747.29369447188969389, 904.76506767616467641 746.56422655414496603, 902.73876790465169506 744.6189787734924721, 903.10836794813531014 738.4959149305276469, 909.965278531365243 715.03895578185358772))");
				Q2.setText("Polygon ((932.4503702659993678 710.56818313477924676, 946.0186041077555501 684.71907909311289586, 958.68682233873005316 674.29728773242709394, 972.63201132314020469 671.92190611627131602, 978.34545570971511097 679.61551318884789907, 979.61324330652439585 687.91110357542618203, 979.2118478789150231 695.70014508377175844, 978.44122091149188236 702.41211204753801667, 979.36751469385740165 706.72854432652002288, 976.54506807043003391 714.22144767861823311, 967.57241462362674156 721.17246096067196959, 953.55784171455206888 726.71113613842362611, 946.71206106563249705 731.82014465729207586, 943.59623950511331714 738.04523826288630062, 941.25498631411483075 740.59626443417869268, 938.684763640097799 742.28562162740399799, 935.52075032066886706 742.37160522305021004, 933.06284195302146145 741.01198536867400435, 931.84754807543095012 734.99936731925004096, 932.4503702659993678 710.56818313477924676))");

				test_desc_tp.setText("MR A and MR B are initially disjoint, then intersect and become disjoint again.  The regions intersect, but none contains the other.");
	            jp.repaint();
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
				if(show_footprint) {
					show_footprint = false;
					return;
				}
				
				 if(mr_p_i == null)
					 return;
			
				show_m_region_evolution_bt.setEnabled(false);
				show_m_region_evolution_slider.setEnabled(false);
				save_to_picture_bt.setEnabled(false);		
				geom_to_show_id = 0;
				
			    show_footprint = true;
			    show_granularity = Integer.parseInt(step.getText());
			    
			    play_task = new TimerTask() 
			    {
			        public void run() 
			        {
			        	jp.repaint();
			        	
			    		if(geom_to_show_id < max - 1) 
			    			geom_to_show_id += show_granularity;
			    		
			    			if(geom_to_show_id > max - 1)
			    			{
				    			timer.cancel();
				    			
								//show_m_region_evolution_slider.setValue(show_m_region_evolution_slider.getMaximum());
								show_m_region_evolution_bt.setEnabled(true);
								show_m_region_evolution_slider.setEnabled(true);
								save_to_picture_bt.setEnabled(true);
			    			}
			    		else {
			    			timer.cancel();
			    			
							//show_m_region_evolution_slider.setValue(show_m_region_evolution_slider.getMaximum());
							show_m_region_evolution_bt.setEnabled(true);
							show_m_region_evolution_slider.setEnabled(true);
							save_to_picture_bt.setEnabled(true);
			    		}
			        }
			    };
			    
			    //show_footprint = false;
				timer = new Timer();
				timer.scheduleAtFixedRate(play_task, 0, Long.parseLong(rate.getText()));				
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
    	
    	btn_Intersects.addActionListener(new ActionListener() 
    	{
			public void actionPerformed(ActionEvent arg0) 
			{
				//mr_p_i = null;

				boolean pass_through_control_points = pass_through_control_points_cb.isSelected();
				boolean show_intersection_information = print_intersection_information_cb.isSelected();
				boolean show_solver_exec_time = print_solver_execution_time_cb.isSelected();
				
				int num_samples = Integer.parseInt(n_samples_tx.getText());
				String interval = i_b_tx.getText() + "," + i_e_tx.getText();

				String prec = s_precision_tx.getText();
				String n_dec_dig = n_dec_dig_tx.getText();
				
				int op_id = op_cb.getSelectedIndex();
				
				//String op = String.valueOf(op_id + 1);
				String op = String.valueOf(1);

				String[] cmd = new String[14];
				
				cmd[0] = "python";
				cmd[1] = "D:\\java\\mr_mr_predicates.py";				
			
				cmd[2] = p1.getText();
				cmd[3] = q1.getText();

				cmd[4] = P2.getText();
				cmd[5] = Q2.getText();
				
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
				
				String[] arr = new String[2];
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
					JOptionPane.showMessageDialog(null, arr[0], "Intersects", JOptionPane.INFORMATION_MESSAGE);
					jp.repaint();
					return;
				}

				execution_time = arr[1];
				predicate = arr[0];				
				shoe_predicate_info = true;

    			//((DrawGraphs) jp).reset();
	            jp.repaint();
			}
		});

    	query_bt.addActionListener(new ActionListener() 
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
				
				String op = String.valueOf(op_id + 1);

				/*
				if(op_id == 0)
					operation = "Intersect(MR, MR, I)";
				else if(op_id == 1)
					operation = "Touch(MR, MR, I)";
				else if(op_id == 2)
					operation = "Equal(MR, MR, I)";
				else if(op_id == 3)
					operation = "Disjoint(MR, MR, I)";
				else if(op_id == 4)
					operation = "Contains(MR, MR, I)";
				else if(op_id == 5)
					operation = "Within(MR, MR, I)";
				else if(op_id == 6)
					operation = "Overlap(MR, MR, I)";
				else {
					JOptionPane.showMessageDialog(null, "Operation mot implemented.", "Operation", JOptionPane.INFORMATION_MESSAGE);
					jp.repaint();
					return;
				}
				*/
				
				String[] cmd = new String[14];
				
				cmd[0] = "python";
				cmd[1] = "D:\\java\\mr_mr_pred.py";				
			
				cmd[2] = p1.getText();
				cmd[3] = q1.getText();

				cmd[4] = P2.getText();
				cmd[5] = Q2.getText();
				
				
				// disjoint
				/*
				cmd[2] = "POLYGON((975.0420063220051 697.090167065809, 968.2376237623762 719.366754617414, 949.8141049487542 719.682075626039, 947.5206593693675 726.5578738835004, 929.1730947342762 738.0175376459358, 929.5007298170459 743.256241080192, 924.3364137823626 741.690195051915, 919.6716773339609 738.3449566105769, 912.7913405958017 741.619146256987, 901.9793828644084 732.4514152470385, 891.8226952985542 721.3191704492442, 884.6147234776257 716.73530494427, 877.4067516566968 712.1514394392957, 873.1474955806933 721.3191704492442, 868.8882395046899 730.4869014591925, 851.6435643564355 749.7625329815303, 845.7678029771724 751.5623397481193, 839.0734469726663 758.972351382961, 829.2443944895814 769.7771772161138, 823.6745980825001 760.609446206166, 814 751.4999999999998, 811.0891089108911 744.6965699208442, 802.3783177024834 736.3804428227309, 798 736, 769.3716535620496 707.0652770818208, 757.5275973847811 695.0944675046978, 734.5578555691986 671.8789067884509, 719.8142768445714 645.3579706525286, 721.7800873411885 635.8628206779392, 723.7458978378055 621.1289672690934, 735.4026288700353 597.7088326122334, 738 589, 763.0621077701443 576.5999880779154, 814 568, 845.6261486280558 565.4677432801209, 852 570, 878.7172919877744 575.2903122193516, 892.7049504950495 586.1319261213721, 901.829702970297 592.211081794195, 907.3811614420508 597.0972549398289, 928 614.0000000000002, 975.0420063220051 697.090167065809))";
				cmd[3] = "POLYGON((965 635, 963.1683168316831 648.4432717678101, 958.0990099009902 658.5751978891822, 947.960396039604 658.5751978891822, 942 675, 932 679, 933.5 683.9999999999998, 935 689, 919.2997169901681 692.9781016562131, 907.4059405940594 688.9709762532982, 897.2673267326733 683.9050131926122, 884.6074998412831 681.6848638401293, 875 680, 875.5385318320745 694.8658276536648, 871 710, 861.6493140294922 728.7013719410154, 858.3483767115072 735.028033248251, 855.0474393935223 741.3546945554867, 851.6115528967149 747.7221555823205, 837.1294340674169 742.0589775899646, 826.2970297029703 734.5646437994724, 816.1584158415842 729.4986807387863, 810.6838257704394 731.3618636044034, 793.0534202391211 721.608612617568, 772.9043853461864 709.6530146337057, 755.3267326732673 704.1688654353561, 741 698, 724.9108910891089 688.9709762532982, 704.6336633663364 668.707124010554, 703 651.0000000000002, 702.6975918911147 637.9194267305304, 705 626, 714.7722772277225 602.8496042216359, 760 570, 795.8811881188119 552.1899736147757, 834.2959760355977 574.0513638167383, 846.5742574257424 562.3218997361478, 878 573.0000000000002, 887.1287128712871 572.4538258575199, 902.3366336633663 582.5857519788917, 950.7825840103793 618.7275457564351, 965 635))";
				cmd[4] = "POLYGON((892.35306594597261665 747.89388402949066403, 917.06000986635353911 752.5446028850917628, 931.30283636163187566 760.68336088239379933, 938.47797773822651379 772.87467253697695924, 936.18453215883982921 779.75047079443834264, 921.71072872195463788 782.19293558954893797, 917.35067979482857936 789.75035372990066662, 913.00028657183486303 794.88279196285293438, 908.33555012343322232 791.53755352151483748, 901.45521338527396438 794.81174316792498757, 890.64325565388071482 785.64401215797647637, 880.48656808802650175 774.51176736018214797, 873.27859626709800978 769.92790185520789237, 865.9021024547412253 767.95010909427048773, 860.08870388523973816 772.6008279498715865, 856.01932488658871989 777.83288666242287945, 853.98463538726332445 774.92618737767213588, 855.72865495811367964 768.24077902274552798, 864.44875281236579667 755.45130216984250637, 892.35306594597261665 747.89388402949066403))";
				cmd[5] = "POLYGON((879.41392092742944442 729.71448703117766854, 889.59586843560805391 719.23611292160808262, 905.30234479740443021 716.51898401674543493, 915.69536819172503783 720.30301183894971473, 919.65333894372611212 729.96845561698000893, 914.43391940942797191 734.93882689411861975, 913.08115780326852473 743.50976093106328335, 907.10894991356440187 745.86812153907453649, 903.46665239345543341 752.06605014146452959, 894.28654149784210858 754.96664410872506323, 886.51609268522088314 753.56158382969033482, 874.69227938276412715 747.81969845663002161, 865.6532279740820286 749.37989383540730159, 862.54327071581406017 752.79927334168314701, 858.65736615717491986 753.99565981920409286, 855.74808947198516762 752.74425405949409651, 855.01914955103779903 748.80008871936524883, 855.73428406011316838 742.3498703605157516, 863.61937324107020686 733.62936271821831724, 879.41392092742944442 729.71448703117766854))"; 
				 */
				
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
								
				n_samples.setText("Nº Samples: " + String.valueOf(max));
				
				show_m_region_evolution_slider.setMinimum(0);
				show_m_region_evolution_slider.setMaximum(max);
				
				Nr = 3;
				
    			((DrawGraphs) jp).reset();
    			((DrawGraphs) jp).adjust_screen_position();		
	            jp.repaint();				
			}
		});
    	
    	/*
    	load_test_bt.addActionListener(new ActionListener() 
    	{
			public void actionPerformed(ActionEvent arg0) 
			{
				mr_p_i = null;

				int idx = tests_cb.getSelectedIndex();
								
				boolean pass_through_control_points = pass_through_control_points_cb.isSelected();
				boolean show_intersection_information = print_intersection_information_cb.isSelected();
				boolean show_solver_exec_time = print_solver_execution_time_cb.isSelected();
				
				int num_samples = Integer.parseInt(n_samples_tx.getText());
				//String interval = i_b_tx.getText() + "," + i_e_tx.getText();

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
					JOptionPane.showMessageDialog(null, "Operation mot implemented.", "Operation", JOptionPane.INFORMATION_MESSAGE);
					jp.repaint();
					return;
				}
				
				String[] cmd = new String[14];
				
				cmd[0] = "python";
				//cmd[1] = "D:\\java\\tests.py";
				cmd[1] = "D:\\java\\mr_mr_pred.py";				
			
				cmd[2] = p1.getText();
				cmd[3] = q1.getText();

				cmd[4] = P2.getText();
				cmd[5] = Q2.getText();
								
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
				cmd[10] = intervals[idx];
				//cmd[8] = interval;
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
								
				n_samples.setText("Nº Samples: " + String.valueOf(max));
				
				show_m_region_evolution_slider.setMinimum(0);
				show_m_region_evolution_slider.setMaximum(max);
				
				Nr = 3;
				
    			((DrawGraphs) jp).reset();
    			((DrawGraphs) jp).adjust_screen_position();		
	            jp.repaint();
			}
		});
    	*/
    	
    	save_all_to_png_bt.addActionListener(new ActionListener() 
		{
			public void actionPerformed(ActionEvent arg0) 
			{
				if(mr_p_i == null)
					return;
				
				show_m_region_evolution_slider.setEnabled(false);
				//play.setEnabled(false);
				
				int v = geom_to_show_id;
				int N = mr_p_i.length / 3;
				
				status.setText("Saving!");
				
				/*
		        if(mr_p_i != null)
		        {
			        int n = mr_p_i.length / 3;
			        
			    	if(i < n)
			    		geom_to_show_id = i;
			    	else if(i == n)
			    		geom_to_show_id = i - 1;
		        }
		        */				
				
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
				//play.setEnabled(true);
				status.setText("");
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
			        int n = mr_p_i.length / 3;
			        
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
				show_footprint = false;
				execution_time = null;
				predicate = null;
				shoe_predicate_info = false;
				
		    	jp.repaint();
		    }
		});
	}
}