#ifndef _E531C953_5C3F_455F_B34E_DF2CA5AD02FA
#define _E531C953_5C3F_455F_B34E_DF2CA5AD02FA


#include <stdlib.h>
#include <limits>

#include <string>
#include <vector>
#include <utility>
#include <map>
#include <list>


namespace {
struct nont
{ } nont;
}

inline void *operator new(unsigned long size, struct nont *)
{
    return malloc(size);
}


template<typename T>
struct malloc_allocator {

    typedef size_t size_type;
    typedef ptrdiff_t difference_type;
    typedef T* pointer;
    typedef const T* const_pointer;
    typedef T& reference;
    typedef const T& const_reference;
    typedef T value_type;

    template <class U> struct rebind { typedef malloc_allocator<U> other; };
    malloc_allocator() throw() {}
    malloc_allocator(const malloc_allocator&) throw() {}

    template <class U> malloc_allocator(const malloc_allocator<U>&) throw(){}

    ~malloc_allocator() throw() {}

    pointer address(reference x) const { return &x; }
    const_pointer address(const_reference x) const { return &x; }

    pointer allocate(size_type s, void const * = 0) {
        if (0 == s)
            return NULL;
        pointer temp = (pointer)malloc(s * sizeof(T));
        if (temp == NULL)
            std::terminate();
        return temp;
    }

    void deallocate(pointer p, size_type) {
        free(p);
    }

    size_type max_size() const throw() {
        // max() is defined as a macro somewhere, so an awkward workaround:
        size_t(*m)() = std::numeric_limits<size_t>::max;
        return m() / sizeof(T);
    }

    void construct(pointer p, const T& val) {
        new((void *)p) T(val);
    }

    void destroy(pointer p) {
        p->~T();
    }

    bool operator==(const malloc_allocator &other) const {
        return true;
    }

    bool operator!=(const malloc_allocator &other) const {
        return false;
    }
};

typedef std::basic_string<char, std::char_traits<char>, malloc_allocator<char> > pstring;

template<typename T>
struct pvector : public std::vector<T, malloc_allocator<char> >
{ };

template<typename K, typename V, typename Cmp=std::less<K> >
struct pmap : public std::map<K, V, Cmp, malloc_allocator<std::pair<K, V> > >
{ };

struct cstr_cmp {
    bool operator()(const char *l, const char *r) {
        return strcmp(l, r) < 0;
    }
};

template<typename T>
struct plist : public std::list<T, malloc_allocator<T> >
{ };



#endif
