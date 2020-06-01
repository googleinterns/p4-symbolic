all: a.out

test.pb.h: test.proto
	protoc --cpp_out=. test.proto

a.out: test.pb.h client.cc
	g++ client.cc test.pb.cc `pkg-config --cflags --libs protobuf`

.PHONY: clean
clean:
	@rm test.pb.cc test.pb.h a.out -rf
