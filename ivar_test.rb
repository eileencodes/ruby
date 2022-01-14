class A
  def initialize
    @x = 1
  end

  def read; @x; end
end

class B < A; end
class C < A; end

#p RubyVM::YJIT.exit_locations.keys
File.write("somefile.dump", Marshal.dump(RubyVM::YJIT.exit_locations))
