#ifndef SFS_INCLUDE_ID_H_
#define SFS_INCLUDE_ID_H_

#include "llvm/Support/raw_ostream.h"

template<class Tag, class impl, impl default_value>
class ID {
 public:
  typedef impl base_type;
	static ID invalid() { return ID(); }

  struct hasher {
    std::size_t operator()(const ID &id) const {
      return std::hash<impl>()(id.val());
    }
  };

	// Defaults to ID::invalid()
	ID() = default;

	// Explicit constructor:
	constexpr explicit ID(impl val) : m_val(val) { }

	// Allow copy
	ID(const ID &) = default;

	// Assignment operator
	ID &operator=(const ID &) = default;

	// Explicit conversion to get back the impl:
	explicit operator impl() const { return m_val; }

	constexpr impl val() const { return m_val; }

	bool operator<(const ID &id) const {
		return m_val < id.m_val;
	}

	bool operator>(const ID &id) const {
		return m_val > id.m_val;
	}

	bool operator>=(const ID &id) const {
		return m_val >= id.m_val;
	}

	bool operator<=(const ID &id) const {
		return m_val <= id.m_val;
	}

	bool valid() const {
		return *this != invalid();
	}

	friend bool operator==(ID a, ID b) { return a.m_val == b.m_val; }
	friend bool operator!=(ID a, ID b) { return a.m_val != b.m_val; }

	template <typename T, class T2, T2 DV>
	friend llvm::raw_ostream &operator<<(llvm::raw_ostream &o, const ID<T, T2, DV> &id);

 private:
	impl m_val = default_value;
};

template<class Tag, class impl, impl default_value>
llvm::raw_ostream &operator<<(llvm::raw_ostream &o,
	 	const ID<Tag, impl, default_value> &id) {
	o << id.m_val;
	return o;
}

#endif  // SFS_INCLUDE_ID_H
