require "stackprof"

class A
  def initialize
    @a = 689
    @b = 3535345
  end

  def multiply
    53457.times do |n|
      @a * @b * n
    end
  end
end

StackProf.run(mode: :wall, out: "stack.dump") do
  A.new.multiply
end

p Marshal.load(File.read("stack.dump"))
