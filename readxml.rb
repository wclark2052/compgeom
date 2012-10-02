require 'rubygems'
require 'hpricot'
require 'ruby-debug'

class Point
  attr_accessor :x, :y
  def initialize(x0,y0)
    @x = x0
    @y = y0
  end
end

class Shape
  attr_accessor :points, :id
  def initialize(id0, points_arr=[])  # point arr is array of 2-d arrays, representing points, ordered
    @id = id0
    @points = Array.new
    points_arr.each do |point|
      p = Point.new(point[0],point[1])
      @points.push(p)
    end
  end
  def segments # array of 2-d arrays, each of which represents a segment and contains endpoints
    segs = []
    @points.each_with_index do |p, i|
      new_i = case (i == @points.length() - 1)
        when true then 0
        else i+1
      end
      segs.push([p, @points[new_i]])
    end
    segs
  end
end


def point_in_shape(point,shape) # uses ray-casting algorithm
  #find offset, as we can represent ray as a segment that continues from point of origin by a large enough offset so as to definitely pass any edge that might contain it
  xoffset = 0
  yoffset = 0
  shape.points.each do |pt|
    if (pt.x - point.x).abs > xoffset
      xoffset = (pt.x - point.x).abs
    end
    if (pt.y - point.y).abs > yoffset
      yoffset = (pt.y - point.y).abs
    end
  end
  x0 = point.x
  y0 = point.y
  x1 = x0 + xoffset*2
  y1 = y0 + yoffset*2
  # now the ray starts from (x0 and y0), and goes through (x1,y1) to (+inf,+inf), but we only consider the segment of it that ends at (x1,y1)
  m0 = (y1-y0).to_f / ((x1-x0).to_f)
  b0 = y0 - m0*(x0.to_f)
  intersects_points = false
  shape.points.each do |p|
    if p.y.to_f == (m0*(p.x.to_f) + b0.to_f)
      intersects_points = true
    end
  end
  if intersects_points
    while intersects_points do
      y1 += 1 # edge the ray up by increasing the upper-right endpoint's y-coordinate by one unit
      m0 = (y1-y0).to_f / ((x1-x0).to_f)
      b0 = y0.to_f - m0*(x0.to_f)   
      intersects_points = false
      shape.points.each do |p|
        if p.y.to_f == m0*(p.x.to_f) + b0.to_f
          intersects_points = true
        end     
      end
    end
  end
  ray_segment = [Point.new(x0,y0),Point.new(x1,y1)]
  edges_touched = 0
  shape.segments.each do |shape_segment|
    intsc = Intersection.new(shape_segment, ray_segment)
    if intsc.did_intersect
      edges_touched += 1 
    end
  end
  edges_touched.odd?
end


class Line
  attr_accessor :m, :b, :vert, :x_int # y = mx + b; or vert=true if vertical, with x_int as defined x-intercept
  def initialize(seg) # seg is a 2-d array of points, representing a segment
    x0 = seg[0].x
    y0 = seg[0].y
    x1 = seg[1].x
    y1 = seg[1].y
    vert0 = (x0 == x1)
    case vert0
      when true
        m0 = nil
        b0 = nil
        x_int0 = x0
      else
        m0 = (y1-y0).to_f/((x1-x0).to_f)
        b0 = y0.to_f - m0*(x0.to_f)
        x_int0 = nil
    end
    @m = m0
    @b = b0
    @x_int = x_int0
    @vert = vert0
  end 
end

def point_in_x_range(point,segment)
  (([segment[0].x,segment[1].x]).min <= point.x) && (point.x <= ([segment[0].x,segment[1].x]).max)
end

def point_in_y_range(point,segment)
  (([segment[0].y,segment[1].y]).min <= point.y) && (point.y <= ([segment[0].y,segment[1].y]).max)
end

class Intersection
  attr_accessor :x, :y, :did_intersect, :tangent
  def initialize(seg1, seg2) # arguments are segments represented as 2-d arrays of points
    intersect = false
    is_tangent = nil
    xf = nil
    yf = nil
    line1 = Line.new(seg1)
    line2 = Line.new(seg2)
    if line1.vert && line2.vert # both are vertical
      if line1.x_int != line2.x_int
        intersect = false
        xf = nil
        yf = nil
      else
        intersect = point_in_y_range(seg2[0],seg1) || point_in_y_range(seg2[1],seg1) # arbitrary -- we could alternately test that segment 2 contains either endpoint of segment 1
        case intersect
        when true
          is_tangent = true
          xf = line1.x_int
          yf = nil
        else
          xf = nil
          yf = nil
        end
      end
    elsif line1.vert && !line2.vert # only line1 is vertical
      x0 = line1.x_int
      y0 = line2.m*(x0.to_f) + (line2.b.to_f)
      int_pt = Point.new(x0,y0)
      intersect = point_in_x_range(int_pt,seg1) && point_in_x_range(int_pt,seg2) && point_in_y_range(int_pt,seg1) && point_in_y_range(int_pt,seg2)
      case intersect
      when true
        xf = x0
        yf = y0
        is_tangent = false
      else
        xf = nil
        yf = nil
      end
    elsif line2.vert && !line1.vert # only line2 is vertical
      x0 = line2.x_int
      y0 = line1.m*(x0.to_f) + (line1.b.to_f)
      int_pt = Point.new(x0,y0)
      intersect = point_in_x_range(int_pt,seg1) && point_in_x_range(int_pt,seg2) && point_in_y_range(int_pt,seg1) && point_in_y_range(int_pt,seg2)
      case intersect
      when true
        xf = x0
        yf = y0
        is_tangent = false
      else
        xf = nil
        yf = nil
      end
    else # neither is vertical
      m1 = line1.m
      m2 = line2.m
      b1 = line1.b
      b2 = line2.b
      if m1 == m2
        if b1 == b2 # lines containing segments are tangent, the same
          intersect = point_in_x_range(seg2[0],seg1) || point_in_x_range(seg2[1],seg1)
          is_tangent = true
          xf = nil
          yf = nil
        else # are parallel but not tangent
          intersect = false
          xf = nil
          yf = nil
        end
      else # lines containing segments are intersecting and not tangent
        x0 = (b2-b1).to_f / (m1-m2)
        y0 = m1*(x0.to_f) + (b1.to_f)
        int_pt = Point.new(x0,y0)
        intersect = point_in_x_range(int_pt,seg1) && point_in_x_range(int_pt,seg2) && point_in_y_range(int_pt,seg1) && point_in_y_range(int_pt,seg2)
        case intersect
        when true
          xf = x0
          yf = y0
          is_tangent = false
        else
          xf = nil
          yf = nil
        end
      end      
    end
    @x = xf
    @y = yf
    @did_intersect = intersect
    @tangent = is_tangent
  end
end


def combinations(a1,a2) #args are arrays; returns array of combinations of all indices between each
  return_a = []
  a1.each_index do |i|
    a2.each_index do |j|
      return_a.push([i,j])
    end
  end
  return_a
end

def combine_two_from(a1)
  used = []
  combinations = []
  a1.each_index do |i|
    used.push(i)
    a1.each_index do |j|
      if !used.include?(j)
        combinations.push([i,j])
      end
    end
  end
  combinations
end

def read_xml(str)
  fl = File.open(str, "r")
  doc = Hpricot(fl)
  fl.close
  doc
end

xmlstr = ARGV[0]
doc = read_xml(xmlstr)
shapes = []
doc.search("/geometry").search("/shape").each do |shapexml|
  points = []
  shapexml.search("/point").each do |pointxml|
    points.push([pointxml.attributes["x"].to_i, pointxml.attributes["y"].to_i])
  end
  shape_id = shapexml.attributes["id"]
  shapes.push(Shape.new(shape_id, points))
end

output = ""
combined_shapes = combine_two_from(shapes).each do |shape_comb|
  shapes_intersect = false
  shape1 = shapes[shape_comb[0]]
  shape2 = shapes[shape_comb[1]]
  combined_indices = combinations(shape1.segments, shape2.segments)  
  segs_intersect = false
  combined_indices.each do |i_comb|
    seg1 = shape1.segments[i_comb[0]]
    seg2 = shape2.segments[i_comb[1]]
    int = Intersection.new(seg1,seg2)
    if int.did_intersect
      segs_intersect = true
    end
  end
  if segs_intersect
    output += "Shape #{shape1.id} and shape #{shape2.id} intersect; "
  elsif point_in_shape(shape1.points[0],shape2)
      output += "Shape #{shape2.id} contains shape #{shape1.id}; "
  elsif point_in_shape(shape2.points[0],shape1)
      output += "Shape #{shape1.id} contains shape #{shape2.id}; "
  else
      output += "Shapes #{shape1.id} and #{shape2.id} do not touch; "
  end
end


p output

shapes
