package gui;

public class Data {

	private int type;
	private Object data;
	private String ref_obj_wkt;
	private Main m;
	//private InterpolationMethod interpolation_method;
	private boolean cw;
	private double threshold;
	private String[] ref_objects_wkt;
	
	public Data(int type, Object data, String ref_obj_wkt, Main m, double threshold, boolean cw, String[] ref_objects_wkt) 
	{
		this.type = type;
		this.data = data;
		this.ref_obj_wkt = ref_obj_wkt;
		this.m = m;
		//this.interpolation_method = interpolation_method;
		this.cw = cw;
		this.threshold = threshold;
		this.ref_objects_wkt = ref_objects_wkt;
	}
	
	public int get_type() {
		return type;
	}
	
	public Object get_data() {
		return data;
	}
	
	public String[] get_ref_objects_wkt() {
		return ref_objects_wkt;
	}
	
	public String get_ref_obj_wkt() {
		return ref_obj_wkt;
	}	
	
	public Main get_main() {
		return m;
	}
	
	/*
	public InterpolationMethod get_interpolation_method() {
		return interpolation_method;
	}
	*/
	
	public double get_threshold() {
		return threshold;
	}
	
	public boolean get_cw() {
		return cw;
	}
}