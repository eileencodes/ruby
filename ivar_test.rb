class A
  def initialize
    @x = 1
  end

  def read; @x; end
end

class B < A; end
class C < A; end
