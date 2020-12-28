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
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Timer;
import java.util.TimerTask;
import java.awt.event.ActionEvent;
import javax.swing.JTextField;
import java.awt.Color;
import javax.swing.JSlider;

import javax.swing.event.ChangeListener;
import javax.swing.JLabel;
import javax.swing.JCheckBox;
import java.awt.Font;

public class VLDB extends JFrame 
{
	private static final long serialVersionUID = 6237268416941231840L;
	
	private JPanel contentPane;
	
	private JPanel viz_p;
	
	private Data d;
	
	private JFrame f;
	
	private JPanel jp;
	
	private JLabel status;
	
	private JPanel tools_p;
	
	public static final double DEFAULT_ZOOM_MULTIPLICATION_FACTOR = 0.25;
	public static final double DEFAULT_MIN_ZOOM_LEVEL = 0.25;
	public static final double DEFAULT_MAX_ZOOM_LEVEL = 100;
	
    private double zoomLevel = 1.0;
    private double minZoomLevel = DEFAULT_MIN_ZOOM_LEVEL;
    private double maxZoomLevel = DEFAULT_MAX_ZOOM_LEVEL;
    private double zoomMultiplicationFactor = DEFAULT_ZOOM_MULTIPLICATION_FACTOR;
    
    private double threshold;
    
    private int geom_to_show_id = 0;
    
    private GeometryFactory geometryFactory;
    private WKTReader reader;
    
    private String[] geometries;
    private String[] vertices_paths;
    private String[] app_curves;
    private String[] app_segments_curves;
    private String[] self_intersections_during_interpolation;
    private String[] app_vertices_curves;
    private String[] curves_spans_aabbs;
    private String[] curves_aabbs;
    private String[] flatten_curves;
    private String[] curve_seg_intersections;
    private String[] obs_at;
    private String[] curve_curve_aabb_intersections;
    private String[] curve_curve_point_intersections;
    private String[] curves_footprint;
    private String[] discrete_footprint;
    private String[] curve_intersections_info;
    private String[] discrete_union_footprint;
    private String[] footprint;
    private int Nr;
    
    private String[] mr_p_i;
    private int mr_p_i_len;
    
    private String[] ms_ms_i;
    private int ms_ms_i_len;
    
    private String wkt;
    private int max;
    
    private TimerTask play_task;
    
	private int w_center;
	private int h_center;
    
	private double cx = 0;
	private double cy = 0;

    private Timer timer;

    private int show_granularity;
    private boolean show_footprint;
    
    private boolean show_bbox;
    private JLabel method_info_lbl;
    private boolean show_m_region;
    private int n_samples_per_span;
    private int n_segments_per_span;
    private double seg_i_x;
    private double seg_i_y;
    private double seg_e_x;
    private double seg_e_y;
    private double t;
    private Geometry geometry;
    private JButton mr_p_i_bt;
    private JButton mr_p_i2_bt;
    private boolean draw_geom;
    private String intersection_info;
    private String solver_execution_time;
    private JButton mr_ms_bt;
    private JButton btnMsMs;
    private JButton btnMsMs2;
    private JButton intersection_bt;
    
	public VLDB(Data d) 
	{
		/**
		  invalid interpolation
		  
		  POLYGON((949 781, 926 812, 823 766, 804 736, 810 642, 881 555, 886.5 563.5, 892 572, 909 576, 914 583, 922 580, 924.00000005960464 585.66666683554649, 926.00000011920929 591.33333367109299, 928 597, 924 618.5, 920 640, 928.66666692495346 640, 937.33333384990692 640, 946 640, 990 655, 949 781))
		  POLYGON((972 774, 955 806, 922 817, 905 816, 850 782, 822 755, 812 697, 812 656, 835 582, 848 565, 863 562, 876 576, 893 576, 899 583, 909 579, 917 592, 916 637, 962 632, 968 638, 990 640, 972 774))
		 */
		
		this.d = d;
		f = this;
		mr_p_i = null;
		Nr = 0;
		
	    ms_ms_i = null;
	    ms_ms_i_len = 0;
	    
	    intersection_info = null;
	    solver_execution_time = null;
				
		geom_to_show_id = 0;
		draw_geom = true;
		
		geometryFactory = JTSFactoryFinder.getGeometryFactory(null);
	    reader = new WKTReader(geometryFactory);
		
	    //geometries = (String[]) d.get_data();
	    geometries = null;
	    
	    wkt = null;
	    
	    vertices_paths = null;
	    show_m_region = true;
	    app_curves = null;
	    app_segments_curves = null;
	    self_intersections_during_interpolation = null;
	    app_vertices_curves = null;
	    curves_spans_aabbs = null;
	    curves_aabbs = null;
	    flatten_curves = null;
	    curve_seg_intersections = null;
	    obs_at = null;
	    curve_curve_aabb_intersections = null;
    	curve_curve_point_intersections = null;
    	curves_footprint = null;
    	discrete_footprint = null;
    	curve_intersections_info = null;
    	geometry = null;
    	discrete_union_footprint = null;
    	footprint = null;
    	
	    //max = geometries.length - 1;
	    
	    seg_i_x = 0;
	    seg_i_y = 0;
	    seg_e_x = 0;
	    seg_e_y = 0;
	    t = 0;
	    
	    show_bbox = false;
	    
	    //threshold = d.get_threshold();
	    
		draw_UI();
			
		w_center = (int) (viz_p.getWidth() / 2);
		h_center = (int) (viz_p.getHeight() / 2);
		
		n_samples_per_span = 4;
		n_segments_per_span = 3;
	
		// Show the name of the method being used.
			    
		add_listeners();
		
		draw_geometry();
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
			if(mr_p_i == null && ms_ms_i == null)
				return;
			
			
			if(mr_p_i != null)
			{
				try {
					geometry = reader.read(mr_p_i[0]);
				} catch (ParseException e) {
					e.printStackTrace();
				}
			}
			else if(ms_ms_i != null)
			{
				try {
					geometry = reader.read(ms_ms_i[0]);
				} catch (ParseException e) {
					e.printStackTrace();
				}
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
		setTitle("VLDB");
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
		
		status = new JLabel("");
		tools_p.add(status);
	    
	    method_info_lbl = new JLabel("");
	    method_info_lbl.setForeground(Color.RED);
	    method_info_lbl.setFont(new Font("Tahoma", Font.ITALIC, 11));
	    method_info_lbl.setBounds(1117, 131, 145, 27);
	    contentPane.add(method_info_lbl);
	    
	    mr_p_i_bt = new JButton("(MP, MR) Predicates");
	    mr_p_i_bt.setFont(new Font("Tahoma", Font.BOLD, 11));
	    mr_p_i_bt.setBounds(10, 135, 155, 23);
	    contentPane.add(mr_p_i_bt);
	    
	    mr_p_i2_bt = new JButton("(MR, MR) Predicates");
	    mr_p_i2_bt.setFont(new Font("Tahoma", Font.BOLD, 11));
	    mr_p_i2_bt.setBounds(10, 110, 155, 23);
	    contentPane.add(mr_p_i2_bt);
	    
	    mr_ms_bt = new JButton("(MS, MR) 1");
	    mr_ms_bt.setBounds(10, 160, 155, 23);
	    contentPane.add(mr_ms_bt);
	    mr_ms_bt.setFont(new Font("Tahoma", Font.BOLD, 11));
	    
	    btnMsMs = new JButton("(MS, MR) 2");
	    btnMsMs.setBounds(10, 185, 155, 23);
	    contentPane.add(btnMsMs);
	    btnMsMs.setFont(new Font("Tahoma", Font.BOLD, 11));
	    
	    btnMsMs2 = new JButton("(MT. MR)");
	    btnMsMs2.setBounds(10, 210, 155, 23);
	    contentPane.add(btnMsMs2);
	    btnMsMs2.setFont(new Font("Tahoma", Font.BOLD, 11));
	    
	    intersection_bt = new JButton("MRs Intersection");
	    intersection_bt.setBounds(10, 235, 155, 23);
	    contentPane.add(intersection_bt);
	    intersection_bt.setFont(new Font("Tahoma", Font.BOLD, 11));
	}

	public void add_listeners()
	{
        addWindowListener(new WindowAdapter() 
        {
            @Override
            public void windowClosing(WindowEvent e) 
            {
                setVisible(false);
                dispose();
            }
        });
        
        intersection_bt.addActionListener(new ActionListener() 
    	{
			public void actionPerformed(ActionEvent arg0) 
			{
				VIZI msmp = new VIZI(d);
				msmp.setVisible(true);
				jp.repaint();
			}
		});
        
        mr_ms_bt.addActionListener(new ActionListener() 
    	{
			public void actionPerformed(ActionEvent arg0) 
			{
				MRegMS msmp = new MRegMS(d);
				msmp.setVisible(true);
				jp.repaint();
			}
		});
    	
        // mpoint, mregion predicates.
    	mr_p_i_bt.addActionListener(new ActionListener() 
    	{
			public void actionPerformed(ActionEvent arg0) 
			{
				MSegMP msmp = new MSegMP(d);
				msmp.setVisible(true);
				jp.repaint();
			}
		});
    	
    	btnMsMs.addActionListener(new ActionListener() 
    	{
			public void actionPerformed(ActionEvent arg0) 
			{
				MSMS msmp = new MSMS(d);
				msmp.setVisible(true);
				jp.repaint();
			}
		});
    	
    	btnMsMs2.addActionListener(new ActionListener() 
    	{
			public void actionPerformed(ActionEvent arg0) 
			{
				MSMS2 msmp = new MSMS2(d);
				msmp.setVisible(true);
				jp.repaint();
			}
		});
    	
    	mr_p_i2_bt.addActionListener(new ActionListener() 
    	{
			public void actionPerformed(ActionEvent arg0) 
			{
				MRMR msmp = new MRMR(d);
				msmp.setVisible(true);
				jp.repaint();
			}
		});
	}
}