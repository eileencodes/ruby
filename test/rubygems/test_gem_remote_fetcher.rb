# frozen_string_literal: true

require "webrick"
require "net/http"

class TestGemRemoteFetcher < Test::Unit::TestCase
  SERVER_DATA = <<-EOY
--- !ruby/object:Object
gems:
  rake-0.4.11: !ruby/object:Object
    rubygems_version: "0.7"
    specification_version: 1
    name: rake
    version: !ruby/object:Object
      version: 0.4.11
    date: 2004-11-12
    summary: Ruby based make-like utility.
    require_paths:
      - lib
    author: Jim Weirich
    email: jim@weirichhouse.org
    homepage: http://rake.rubyforge.org
    description: Rake is a Make-like program implemented in Ruby. Tasks and dependencies are specified in standard Ruby syntax.
    autorequire:
    bindir: bin
    has_rdoc: true
    required_ruby_version: !ruby/object:Object
      requirements:
        -
          - ">"
          - !ruby/object:Object
            version: 0.0.0
      version:
    platform: ruby
    files:
      - README
    test_files: []
    library_stubs:
    rdoc_options:
    extra_rdoc_files:
    executables:
      - rake
    extensions: []
    requirements: []
    dependencies: []
  EOY

  PROXY_DATA = SERVER_DATA.gsub(/0.4.11/, "0.4.2")

  def test_implicit_upper_case_proxy
    start_servers
    uri = URI("http://localhost:#{proxy_server_port}/yaml")
    response = Net::HTTP.get(uri)
    response
  ensure
    stop_servers
  end

  def test_implicit_proxy
    start_servers
    PROXY_DATA.match(/0\.4\.2/)
  ensure
    stop_servers
  end

  class NilLog < WEBrick::Log
    def log(level, data) # Do nothing
    end
  end

  private

  def start_servers
    @normal_server = start_server(SERVER_DATA)
    @proxy_server  = start_server(PROXY_DATA)
  end

  def stop_servers
    @normal_server.kill.join
    @proxy_server.kill.join
    WEBrick::Utils::TimeoutHandler.terminate
  end

  def proxy_server_port
    @proxy_server[:server].config[:Port]
  end

  def start_server(data)
    null_logger = NilLog.new
    s = WEBrick::HTTPServer.new(
      Port: 0,
      DocumentRoot: nil,
      Logger: null_logger,
      AccessLog: null_logger
    )
    s.mount_proc("/yaml") do |req, res|
      res.body = data
    end
    th = Thread.new do
      s.start
    ensure
      s.shutdown
    end
    th[:server] = s
    th
  end
end
