CXX=g++-15

TARGET = popstar_ai_openmp simulator original_popstar_ai_openmp

all: $(TARGET)

simulator: simulator.cpp Makefile
	$(CXX) $< -Ofast -Wall -Wextra -std=c++2a -DFISH -o $@

popstar_ai_openmp: popstar_ai.cpp Makefile
	$(CXX) $< -Ofast -Wall -Wextra -std=c++2a -lpthread -fopenmp -DFISH -o $@
original_popstar_ai_openmp: original_popstar_ai.cpp Makefile
	$(CXX) $< -Ofast -Wall -Wextra -std=c++2a -lpthread -fopenmp -DFISH -o $@
popstar_ai: popstar_ai.cpp Makefile
	$(CXX) $< -Ofast -Wall -Wextra -std=c++2a -DFISH -o $@

clean:
	rm $(TARGET)
