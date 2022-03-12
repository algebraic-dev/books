class Tree 
  attr_accessor :children, :name

  def initialize(name, children = [])
    @children = children 
    @name = name 
  end

  def visit_all(&fun)
    visit &fun
    @children.each {|node| node.visit_all &fun }
  end

  def visit(&fun)
    fun.call self
  end
end

def singleton_if (val) do 
  return res.is_a?(Array) ? val : [val]
end

def from_hash(hash)
  if hash.is_a? Hash then 
    children = []
    hash.each do |key, val| 
      res = singleton_if (from_hash val)
      children.push(Tree.new(key, res)) 
    end
    return children
  else 
    return Tree.new(hash, [])
  end
end 

tree = from_hash({:a => [1,2,3]})
tree.each do |n| n.visit_all do |k| puts k.name end end