#pragma once
#include "geometric.h"
#include <queue>
#include <vector>
#include <map>
#include <unordered_map>
#include <optional>
#include <limits>
#include <exception>
#include <stdexcept>
#include <tuple>
#include <utility>
#include <algorithm>
#include <cassert>
#include <memory>
#include <random>


namespace planarity {
    class Point {
    public:
        long x;
        long y;

        bool operator==(const Point &b) const {
            return x == b.x && y == b.y;
        }

        bool operator<(const Point &other) const noexcept {
            return x < other.x || (x == other.x && y < other.y);
        }

        Point(long x, long y) : x(x), y(y) {

        }
    };

    class Line {
    public:
        Point p;
        Point q;

        static inline bool ranges_overlap(std::int64_t min1, std::int64_t max1, std::int64_t min2, std::int64_t max2) {
            if (min1 < min2) {
                return max1 >= min2;
            } else {
                return max2 >= min1;
            }
        }

        Line(long x1, long y1, long x2, long y2) : p(min(Point(x1, y1), Point(x2, y2))),
                                                   q(max(Point(x1, y1), Point(x2, y2))) {
        }

        [[nodiscard]] std::pair<Point, Point> left_and_right() const noexcept {
            if (p < q) {
                return {p, q};
            } else {
                return {q, p};
            }
        }

        [[nodiscard]] inline int orientation(const Point &r) const {
            auto result = (q.y - p.y) * (r.x - q.x) - (q.x - p.x) * (r.y - q.y);
            if (result < 0)
                return -1;
            if (result > 0)
                return 1;
            return 0;
        }

        [[nodiscard]] bool intersects(const Line &b) const {
            auto &s1 = this->p < b.p ? *this : b;
            auto &s2 = !(this->p < b.p) ? *this : b;

            if (s1.p == s2.p) {
                return s1.orientation(s2.q) == 0;
            }
            if (s1.q == s2.q) {
                return !Line(s1.p.x, s1.p.y, s2.p.x, s2.p.y).orientation(s1.q);
            }
            if (s1.q == s2.p) {
                return false;
            }

            auto o1 = s1.orientation(s2.p);
            auto o2 = s1.orientation(s2.q);
            auto o3 = s2.orientation(s1.p);
            auto o4 = s2.orientation(s1.q);

            if (o1 != o2 && o3 != o4) { // general case
                return true;
            }
            if (!o1 && !o2) { // all collinear
                std::int64_t mnxr1 = (std::min)(s1.p.x, s1.q.x), mxxr1 = (std::max)(s1.p.x, s1.q.x);
                std::int64_t mnyr1 = (std::min)(s1.p.y, s1.q.y), mxyr1 = (std::max)(s1.p.y, s1.q.y);
                std::int64_t mnxr2 = (std::min)(s2.p.x, s2.q.x), mxxr2 = (std::max)(s2.p.x, s2.q.x);
                std::int64_t mnyr2 = (std::min)(s2.p.y, s2.q.y), mxyr2 = (std::max)(s2.p.y, s2.q.y);
                if (ranges_overlap(mnxr1, mxxr1, mnxr2, mxxr2) &&
                    ranges_overlap(mnyr1, mxyr1, mnyr2, mxyr2)) {
                    return true;
                }
            }
            return false;
        }
    };

    inline int orientation(Point p1, Point p2, Point p3) {
        std::int64_t v1 = (p2.y - p1.y) * (p3.x - p2.x);
        std::int64_t v2 = (p2.x - p1.x) * (p3.y - p2.y);
        if(v1 == v2) {
            return 0; // collinear
        }
        return (v1 > v2) ? -1 : 1; // clockwise (-1) or counterclockwise (1)
    }

    inline std::int64_t cross(Point p1, Point p2) noexcept {
        return p1.x * p2.y - p2.x * p1.y;
    }

    inline bool collinear_order_correct(Point p1, Point p2, Point p3) noexcept {
        if(p1.x == p2.x) {
            return p1.y > p2.y ? p3.y <= p2.y : p2.y <= p3.y;
        }
        if(p1.x < p2.x) {
            return p2.x <= p3.x;
        } else {
            return p3.x <= p2.x;
        }
    }

    /**
* Compute an approximate intersection point for the two given segments.
*/
    inline std::array<double, 2> approximate_intersection_point(Line s1, Line s2) {
        Point p = s1.p;
        Point r{s1.q.x - s1.p.x, s1.q.y - s1.p.y};
        Point q = s2.q;
        Point s{s2.q.x - s2.p.x, s2.q.y - s2.p.y};
        Point qmp{q.x - p.x, q.y - p.y};
        std::int64_t qpr = cross(qmp, r);
        std::int64_t rs = cross(r, s);
        if(!qpr && !rs) { // collinear
            if(collinear_order_correct(s1.p, s2.p, s1.q)) {
                return {(double)s2.p.x, (double)s2.p.y};
            } else if(collinear_order_correct(s1.p, s2.q, s1.q)) {
                return {(double)s2.q.x, (double)s2.q.y};
            } else if(collinear_order_correct(s2.p, s1.p, s2.q)) {
                return {(double)s1.p.x, (double)s1.p.y};
            } else if(collinear_order_correct(s1.p, s1.q, s2.q)) {
                return {(double)s1.q.x, (double)s1.q.y};
            } else {
                throw std::runtime_error("Overlap check positive, but no overlap!");
            }
        } else if(!rs) {
            // no intersection?!
            throw std::runtime_error("Intersection check positive, but no intersection!");
        } else {
            double u = (double)qpr / rs;
            double x = q.x + u * s.x;
            double y = q.y + u * s.y;
            return {x,y};
        }
    }



    /**
     * Do the given segments intersect? If yes, an approximate intersection point is returned.
     * Both s1 and s2 must have si.s <= si.t.
     */
    inline std::optional<std::array<double, 2>> do_intersect(Line s1, Line s2) {
        std::array<double, 2> result;
        if(s2.p < s1.p) {
            std::swap(s1, s2);
        }
        if(s1.p == s2.p) {
            if(!orientation(s1.p, s1.q, s2.q)) {
                if(collinear_order_correct(s1.p, s1.q, s2.q)) {
                    result[0] = s1.q.x;
                    result[1] = s1.q.y;
                } else {
                    result[0] = s2.q.x;
                    result[1] = s2.q.y;
                }
                return result;
            }
            return {};
        }
        if(s1.q == s2.q) {
            if(!orientation(s1.p, s2.p, s1.q)) {
                result[0] = s2.p.x;
                result[1] = s2.p.y;
                return result;
            }
            return {};
        }
        if(s1.q == s2.p) {
            return {};
        }
        int o1 = orientation(s1.p, s1.q, s2.p),
                o2 = orientation(s1.p, s1.q, s2.q),
                o3 = orientation(s2.p, s2.q, s1.p),
                o4 = orientation(s2.p, s2.q, s1.q);
        if(o1 != o2 && o3 != o4) { // general case
            return approximate_intersection_point(s1, s2);
        }
        if(!o1 && !o2) { // all collinear
            std::int64_t mnxr1 = (std::min)(s1.p.x, s1.q.x), mxxr1 = (std::max)(s1.p.x, s1.q.x);
            std::int64_t mnyr1 = (std::min)(s1.p.y, s1.q.y), mxyr1 = (std::max)(s1.p.y, s1.q.y);
            std::int64_t mnxr2 = (std::min)(s2.p.x, s2.q.x), mxxr2 = (std::max)(s2.p.x, s2.q.x);
            std::int64_t mnyr2 = (std::min)(s2.p.y, s2.q.y), mxyr2 = (std::max)(s2.p.y, s2.q.y);
            if(Line::ranges_overlap(mnxr1, mxxr1, mnxr2, mxxr2) &&
               Line::ranges_overlap(mnyr1, mxyr1, mnyr2, mxyr2))
            {
                return approximate_intersection_point(s1, s2);
            }
        }
        return {};
    }



/**
 * Prepare a vector of segments (in-place),
 * making sure that each segments start point s
 * is to the left (or below) its end point t.
 */
inline void prepare_segments(std::vector<Line>& segments) {
    for(Line& s : segments) {
        std::tie(s.q, s.p) = s.left_and_right();
    }
}

/**
 * Draw a random bit with uniform probability.
 * Only uses one RNG call per 64 drawn bits.
 */
inline bool draw_random_bit() {
	struct RngContext {
		RngContext() : rng(std::random_device{}()),
						bits(0),
						nbits(0)
		{}

		bool take() noexcept {
			if(nbits == 0) {
				bits = rng();
				nbits = 64;
			}
			bool res = (bits & 1) != 0;
			bits >>= 1;
			--nbits;
			return res;
		}

		std::mt19937_64 rng;
		std::uint64_t bits;
		unsigned nbits;
	};
	static thread_local RngContext rng;
	return rng.take();
}

/**
 * Implements the Bentley-Ottmann sweep-line algorithm
 * to determine whether a set of segments contains a pair of
 * crossing segments (without approximation).
 * Segments are only counted as intersecting if they share
 * a point that is not an endpoint for at least one of them.
 */
class BentleyOttmannAnyIntersection {
public:
	/**
	 * Information about an intersection (segment indices
	 * and approximate location of the intersection).
	 */
	struct Intersection {
		std::size_t segment_index[2];
		double approximate_location[2];
	};

	/**
	 * Create an instance of the algorithm with a vector of segments.
	 * Does not make a copy of the vector.
	 */
	BentleyOttmannAnyIntersection(const std::vector<Line>& segments) :
		m_segments(&segments),
		m_segment_in_list(segments.size(), nullptr),
		m_active_head(nullptr),
		m_active_tail(nullptr),
		m_intersection(std::nullopt)

	{
        setup_events();
        skiplist_init();
	}

	~BentleyOttmannAnyIntersection() {
		skiplist_free();
	}

	/**
	 * Perform the actual search for an intersection.
	 */
	std::optional<Intersection> find_intersection() {
//		setup_events();
//		if(m_active_head) {
//			skiplist_free();
//		}
//		skiplist_init();
		m_intersection = std::nullopt;
		while(!m_events.empty()) {
			Event event = m_events.back(); m_events.pop_back();
			if(event.entering) {
				handle_entering(event.segment_index);
			} else {
				handle_exiting(event.segment_index);
			}
			if(m_intersection) {
				break;
			}
		}
		return m_intersection;
	}

private:
	struct SkipNode;

	/**
	 * Check whether the segment given by segment_index intersects the segment given by node.
	 */
	void check_segment_against(std::size_t segment_index, SkipNode* node) {
		std::size_t other_index = node->segment_index;
		Line s = (*m_segments)[segment_index], o = (*m_segments)[other_index];
		auto res = do_intersect(s, o);
		if(res) {
			m_intersection = Intersection{{segment_index, other_index}, {(*res)[0], (*res)[1]}};
		}
	}

	/**
	 * Handle an event in which a segment enters the set of active segments.
	 */
	void handle_entering(std::size_t segment_index) {
		SkipNode* new_node = skiplist_insert(segment_index);
		if(!new_node) return;
		SkipNode *prev = new_node->prev, *next = new_node->next;
		if(prev->prev) {
			check_segment_against(segment_index, prev);
		}
		if(!m_intersection && next->next) {
			check_segment_against(segment_index, next);
		}
	}

	/**
	 * Handle an event in which a segment leaves the set of active segments.
	 */
	void handle_exiting(std::size_t segment_index) {
		SkipNode* rem_node = m_segment_in_list[segment_index];
		SkipNode *prev = rem_node->prev, *next = rem_node->next;
		skiplist_erase(rem_node);
		if(prev->prev && next->next) {
			check_segment_against(prev->segment_index, next);
		}
	}

	/**
	 * Initialize the sweep line data structure that keeps track of the order of the active segments.
	 * In this implementation, we use a skip list for this purpose.
	 */
	void skiplist_init() {
		std::unique_ptr<SkipNode[]> head{SkipNode::allocate(std::numeric_limits<std::size_t>::max(), 1)},
		                            tail{SkipNode::allocate(std::numeric_limits<std::size_t>::max(), 1)};
		m_active_head = head.release();
		m_active_tail = tail.release();
		m_active_head->next = m_active_tail;
		m_active_tail->prev = m_active_head;
	}

	/**
	 * Free all memory allocated to the sweep line data structure.
	 */
	void skiplist_free() {
		SkipNode *ptr = m_active_head;
		while(ptr) {
			SkipNode* next = ptr->next;
			delete[] ptr;
			ptr = next;
		}
		m_active_head = m_active_tail = nullptr;
	}

	/**
	 * Toss a uniform coin to determine the height of a
	 * newly inserted node in our skip list (between 1 and current_max_level+1).
	 */
	static unsigned skiplist_toss_coins(unsigned current_max_level) {
		unsigned i;
		for(i = 0; i < current_max_level; ++i) {
			if(!draw_random_bit()) {
				break;
			}
		}
		return i + 1;
	}

	/**
	 * Reallocate the skip list head and tail in case the maximum height increases.
	 */
	void reallocate_head_and_tail(std::size_t new_level) {
		std::unique_ptr<SkipNode[]> new_head{SkipNode::allocate(m_active_head->segment_index, new_level)},
			                        new_tail{SkipNode::allocate(m_active_tail->segment_index, new_level)};
		new_head[new_level-1].next = &new_tail[new_level-1];
		new_tail[new_level-1].prev = &new_head[new_level-1];
		for(unsigned l = 0; l < new_level-1; ++l) {
			SkipNode* head = &m_active_head[l];
			SkipNode* tail = &m_active_tail[l];
			SkipNode* nhead = &new_head[l];
			SkipNode* ntail = &new_tail[l];
			SkipNode* next = head->next;
			next->prev = nhead;
			nhead->next = next;
			SkipNode* prev = tail->prev;
			prev->next = ntail;
			ntail->prev = prev;
		}
		delete[] m_active_head;
		delete[] m_active_tail;
		m_active_head = new_head.release();
		m_active_tail = new_tail.release();
	}

	/**
	 * Create a new node for insertion into the skiplist; determines the nodes height
	 * and reallocates head and tail if necessary. The node is not linked into the skip list.
	 */
	std::unique_ptr<SkipNode[]> create_new_node(std::size_t segment_index) {
		unsigned current_max = m_active_head->num_levels;
		unsigned new_level = skiplist_toss_coins(current_max);
		std::unique_ptr<SkipNode[]> node{SkipNode::allocate(segment_index, new_level)};
		if(new_level > current_max) {
			reallocate_head_and_tail(new_level);
		}
		return node;
	}

	/**
	 * Logically negate an optional<bool>, returning an empty optional if the input is empty.
	 */
	static std::optional<bool> invert(std::optional<bool> input) noexcept {
		if(!input) {
			return input;
		}
		return !*input;
	}

	/**
	 * Set the m_intersection member that stores the intersection found
	 * to the intersection found between segments si1 and si2.
	 */
	void set_intersection(std::size_t si1, std::size_t si2) {
		auto loc = approximate_intersection_point((*m_segments)[si1], (*m_segments)[si2]);
		m_intersection = Intersection{{si1, si2}, {loc[0], loc[1]}};
	}

	/**
	 * Compare two segments s1 and s2 for insertion into the sweep line data structure
	 * if segment s1 is vertical. Either of the two segments can be the newly inserted segment.
	 */
	std::optional<bool> compare_less_at_x_1vert(std::size_t si1, std::size_t si2, Line s1, Line s2) {
		if(s2.p.x == s1.p.x) {
			if(s2.p.y <= s1.p.y) {
				return false;
			}
			set_intersection(si1, si2);
			return {};
		}
		std::int64_t delta_x_2 = s2.q.x - s2.p.x;
		std::int64_t delta_y_2 = s2.q.y - s2.p.y;
		std::int64_t delta_x_2_to_now = s1.p.x - s2.p.x;
		std::int64_t lhs = delta_x_2_to_now * delta_y_2;
		std::int64_t rhs_bot = delta_x_2 * (s1.p.y - s2.p.y);
		std::int64_t rhs_top = delta_x_2 * (s1.q.y - s2.p.y);
		if(lhs > rhs_top) {
			return true;
		}
		if(lhs < rhs_bot) {
			return false;
		}
		if(s2.q == s1.q) {
			return true;
		}
		set_intersection(si1, si2);
		return {};
	}

	/**
	 * Compare two segments s1 and s2 for insertion into the sweep line data structure.
	 * s1 is the newly-inserted segment, and neither segment is vertical.
	 */
	std::optional<bool> compare_less_at_x_novert(std::size_t si1, std::size_t si2, Line s1, Line s2) {
		if(s2.p.x == s1.p.x) {
			if(s1.p.y > s2.p.y) {
				return false;
			}
			// same start point: order by incline
			std::int64_t dx1 = s1.q.x - s1.p.x, dy1 = s1.q.y - s1.p.y;
			std::int64_t dx2 = s2.q.x - s2.p.x, dy2 = s2.q.y - s2.p.y;
			std::int64_t lhs = dy1 * dx2, rhs = dy2 * dx1;
			if(lhs < rhs) {
				return true;
			}
			if(rhs < lhs) {
				return false;
			}
			// overlap
			set_intersection(si1, si2);
			return {};
		}
		std::int64_t delta_x_1_to_now = s1.p.x - s2.p.x;
		std::int64_t delta_x2 = s2.q.x - s2.p.x, delta_y2 = s2.q.y - s2.p.y;
		std::int64_t lhs = delta_x_1_to_now * delta_y2;
		std::int64_t rhs = delta_x2 * (s1.p.y - s2.p.y);
		if(lhs < rhs) {
			return false;
		}
		if(rhs < lhs) {
			return true;
		}
		set_intersection(si1, si2);
		return {};
	}

	/**
	 * Compare two segments for insertion into the sweep line data structure.
	 * si1 is the index of the newly-inserted segment. Returns an empty
	 * optional if the segments cannot be ordered; in that case, an intersection
	 * is always placed into m_intersections.
	 */
	std::optional<bool> compare_less_at_x(std::size_t si1, std::size_t si2) {
		Line s1 = (*m_segments)[si1], s2 = (*m_segments)[si2];
		bool vert1 = (s1.p.x == s1.q.x), vert2 = (s2.p.x == s2.q.x);
		if(vert1 && vert2) {
			/* since entry events are ordered after exit events, this always is an overlap */
			set_intersection(si1, si2);
			return {};
		}
		if(vert1) {
			return compare_less_at_x_1vert(si1, si2, s1, s2);
		}
		if(vert2) {
			return invert(compare_less_at_x_1vert(si2, si1, s2, s1));
		}
		return compare_less_at_x_novert(si1, si2, s1, s2);
	}

	/**
	 * Search on the current level of the skip list for the first position where our
	 * newly-inserted segment compares less than the next segment (or the next segment is the tail).
	 * Returns true if an intersection was encountered during the search.
	 * Advances the pointers current/n/nn to the corresponding position.
	 */
	bool skiplist_search_level(std::size_t segment_index, SkipNode*& current, SkipNode*& n, SkipNode*& nn) {
		for(;;) {
			nn = n->next;
			if(nn == nullptr) {
				return false;
			} else {
				auto res = compare_less_at_x(segment_index, n->segment_index);
				if(!res) {
					return true;
				}
				if(*res) {
					return false;
				}
			}
			current = n;
			n = nn;
		}
	}

	/**
	 * Insert a new segment into the skip list sweep line intersection data structure.
	 * Returns nullptr if an intersection is found during the insertion process;
	 * that intersection is recorded in m_intersection.
	 */
	SkipNode* skiplist_insert(std::size_t segment_index) {
		std::unique_ptr<SkipNode[]> node = create_new_node(segment_index);
		SkipNode* current = &m_active_head[m_active_head->num_levels - 1];
		unsigned l = m_active_head->num_levels - 1;
		unsigned nl = node[0].num_levels - 1;
		SkipNode *n = current->next, *nn;
		// searching above the new nodes' level
		while(l > nl) {
			if(skiplist_search_level(segment_index, current, n, nn)) {
				return nullptr;
			}
			current -= 1;
			n = current->next;
			--l;
		}
		// searching at or below the new nodes' level
		for(;;) {
			if(skiplist_search_level(segment_index, current, n, nn)) {
				return nullptr;
			}
			node[l].prev = current;
			node[l].next = n;
			if(l-- == 0) {
				break;
			}
			current -= 1;
			n = current->next;
		}
		for(l = 0; l < node[0].num_levels; ++l) {
			node[l].prev->next = &node[l];
			node[l].next->prev = &node[l];
		}
		m_segment_in_list[segment_index] = &node[0];
		return node.release();
	}

	/**
	 * Erase a segment from our skip list sweep line data structure.
	 */
	void skiplist_erase(SkipNode* node) {
		for(unsigned i = 0, l = node->num_levels; i < l; ++i) {
			SkipNode* layer = &node[i];
			SkipNode* prev = layer->prev, *next = layer->next;
			prev->next = next;
			next->prev = prev;
		}
		delete[] node;
	}

	/**
	 * Setup the event priority queue.
	 * Implemented as sorted vector of events
	 * since we need not dynamically add events.
	 */
	void setup_events() {
		m_events.clear();
		std::size_t ind = 0;
		for(const auto& seg : *m_segments) {
			m_events.emplace_back(seg.p, ind, true);
			m_events.emplace_back(seg.q, ind, false);
			++ind;
		}
		std::sort(m_events.begin(), m_events.end());
	}

	/**
	 * A single node of our skip list sweep line data structure.
	 * A skip list node of height h is allocated as array of h
	 * SkipNodes.
	 */
	struct SkipNode {
		/**
		 * Allocate a new SkipNode of height levels.
		 */
		static SkipNode *allocate(std::size_t segment_index, unsigned levels) {
			auto *nodes = new SkipNode[levels];
			for(unsigned i = 0; i < levels; ++i) {
				nodes[i].segment_index = segment_index;
				nodes[i].level = i;
				nodes[i].num_levels = levels;
				nodes[i].prev = nullptr;
				nodes[i].next = nullptr;
			}
			return nodes;
		}

		std::size_t segment_index;
		SkipNode *prev, *next;
		unsigned level, num_levels;
	};

	/**
	 * Represents an event point, i.e., a segment arriving or leaving.
	 */
	struct Event {
		Event(Point p, std::size_t s, bool e) noexcept :
			point(p), segment_index(s), entering(e)
		{}

		bool operator<(const Event& other) const noexcept {
			std::int64_t ox = other.point.x, oy = other.point.y,
				         tx = point.x, ty = point.y;
			if(tx < ox) {
				return false;
			} else if(tx > ox) {
				return true;
			}
			if(ty < oy) {
				return false;
			} else if(ty > oy) {
				return true;
			}
			return entering && !other.entering;
		}

		Point point;
		std::size_t segment_index;
		bool entering;
	};

	const std::vector<Line>* m_segments;
	std::vector<SkipNode*> m_segment_in_list;
	SkipNode *m_active_head, *m_active_tail;
	std::optional<Intersection> m_intersection;
	std::vector<Event> m_events;
};
}

