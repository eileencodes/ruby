class A
  def initialize
    @a = 1
  end

  def extend
    @b = 1
    @c = 2
    @d = 3
    @e = 4
    @f = 1
  end

  def other_reader
    [@b, @c, @d, @e, @f]
  end

  def a; @a; end
end

embedded = A.new
extended = A.new
embedded.extend
extended.other_reader
embedded.other_reader
