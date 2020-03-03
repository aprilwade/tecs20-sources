#ifndef _C3AA62F1_E6B7_491E_9D00_27E6725D8AEB
#define _C3AA62F1_E6B7_491E_9D00_27E6725D8AEB

#include "utilities/stl.hpp"
#include <map>
#include <vector>

// Rapidjson {{{


#define RAPIDJSON_NEW(x) new(&nont) x
#define RAPIDJSON_DELETE(x) free(x)
#include <rapidjson/rapidjson.h>
#include <rapidjson/document.h>
#include <rapidjson/filereadstream.h>
#undef assert
#define assert(p, ...) vmassert(p, __VA_ARGS__)
#include "utilities/debug.hpp"


// }}}

struct Indenter {

    unsigned _indent;

    Indenter(unsigned i)
     : _indent(i)
    { }

    Indenter operator+(unsigned n) const {
      return Indenter(_indent + n);
    };

    const char *operator()(unsigned n = 0) const {
      static char *buffers[80] = { 0 };

      n += _indent;
      assert(n < sizeof(buffers) / sizeof(buffers[0]), "indent overflowed");

      if(buffers[n] != NULL) {
          return buffers[n];
      }

      buffers[n] = (char*)malloc(n + 1);
      memset(buffers[n], ' ', n);
      buffers[n][n] = 0;
      return buffers[n];
    }
};

template<typename T>
struct DataSerializer;

#define DECL_JSON_FIELD_SPEC(TYPE, SERIALIZE, DESERIALIZE) \
    template<> \
    struct DataSerializer<TYPE> \
    { \
        static void serialize_exec(FILE *f, TYPE data) { \
            SERIALIZE \
        } \
        static void deserialize_exec(const rapidjson::Value &json, TYPE &data) { \
            DESERIALIZE \
        } \
    }; \

DECL_JSON_FIELD_SPEC(char, fprintf(f,"%hhd", data);, data = json.GetInt();)
DECL_JSON_FIELD_SPEC(unsigned char, fprintf(f,"%hhu", data);, data = json.GetInt();)
DECL_JSON_FIELD_SPEC(signed char, fprintf(f,"%hhd", data);, data = json.GetInt();)

DECL_JSON_FIELD_SPEC(short, fprintf(f,"%hd", data);, data = json.GetInt();)
DECL_JSON_FIELD_SPEC(unsigned short, fprintf(f, "%hu", data);, data = json.GetInt();)
DECL_JSON_FIELD_SPEC(int, fprintf(f, "%d", data);, data = json.GetInt();)
DECL_JSON_FIELD_SPEC(unsigned int, fprintf(f, "%u", data);, data = json.GetUint();)
DECL_JSON_FIELD_SPEC(long, fprintf(f, "%ld", data);, data = json.GetInt64();)
DECL_JSON_FIELD_SPEC(unsigned long, fprintf(f, "%lu", data);, data = json.GetUint64();)
DECL_JSON_FIELD_SPEC(long long, fprintf(f, "%lld", data);, data = json.GetInt64();)
DECL_JSON_FIELD_SPEC(unsigned long long, fprintf(f, "%llu", data);, data = json.GetUint64();)

DECL_JSON_FIELD_SPEC(float, fprintf(f, "%f", data);, data = json.GetDouble();)
DECL_JSON_FIELD_SPEC(double, fprintf(f, "%f", data);, data = json.GetDouble();)



template<typename Cls>
struct FieldSerializer {

    const char *name;
    char data[sizeof(&FieldSerializer::name)];
    void (*serialization_func)(const Cls *obj, FILE *f, const char *data);
    void (*deserialization_func)(Cls *obj, const rapidjson::Value &json,
                                 const char *data);

    bool compare(const FieldSerializer<Cls> &other) const {
      return memcmp(data, other.data, sizeof(data)) == 0;
    }

    void serialize_to_file(const Cls *obj, FILE *f) const {

      fputc('"', f);
      fputs(name, f);
      fputs("\": ", f);
      serialization_func(obj, f, data);
    }

    void deserialize_from_json(Cls *obj, const rapidjson::Value &json) const {
     deserialization_func(obj, json[name], data);
    }

    template<typename T>
    static FieldSerializer build(const char *name, T (Cls::*field)) {

        FieldSerializer fs;
        fs.name = name;

        assert(sizeof(field) == sizeof(fs.data), "Size mismatch");
        memcpy(fs.data, &field, sizeof(field));

        fs.serialization_func = &FieldSerializer::serialize_data<T>;
        fs.deserialization_func = &FieldSerializer::deserialize_json<T>;

        return fs;
    }

    template<typename T>
    static void serialize_data(const Cls *obj, FILE *f, const char *data) {

        T (Cls::*field);
        memcpy(&field, data, sizeof(field));

        DataSerializer<T>::serialize_exec(f, obj->*field);
    }

    template<typename T>
    static void deserialize_json(Cls *obj, const rapidjson::Value &json,
                                 const char *data) {
      T (Cls::*field);
      memcpy(&field, data, sizeof(field));
      DataSerializer<T>::deserialize_exec(json, obj->*field);
    }
};


template<typename Cls>
struct Serializer {

    const FieldSerializer<Cls> *_fields;
    size_t _fields_len;

    const FieldSerializer<Cls> *_skipped;
    size_t _skipped_len;

    Serializer(const FieldSerializer<Cls> *fields, size_t len)
     : _fields(fields), _fields_len(len), _skipped(NULL), _skipped_len(0)
    { }

    template<size_t N>
    Serializer(const FieldSerializer<Cls> (&fields)[N])
     : _fields(fields), _fields_len(N), _skipped(NULL), _skipped_len(0)
    { }

    void serialize_to_file(const Cls *obj, const Indenter &indent, FILE *f) const {

        fputs("{\n", f);

        for(size_t i = 0; i < _fields_len; i++) {
            fputs(indent(2), f);
            _fields[i].serialize_to_file(obj, f);

            if(i != _fields_len - 1) {
              fputc(',', f);
            }
              fputc('\n', f);
        }

        fputs(indent(), f);
        fputc('}', f);
    }

    void deserialize_from_json(Cls *obj, const rapidjson::Value &json) const {
      for(size_t i = 0; i < _fields_len; i++) {

        bool skip = false;
        for(size_t k = 0; k < _skipped_len; k++) {
          if(_fields[i].compare(_skipped[k])) {
            skip = true;
            break;
          }
        }
        if(skip) {
          continue;
        }

        _fields[i].deserialize_from_json(obj, json);
      }
    }

    template<size_t N>
    void skip_fields(const FieldSerializer<Cls> (&fields)[N]) {
        this->_skipped = fields;
        this->_skipped_len = N;
    }
};


class Klass;
class Method;
class MethodData;
class MethodCounters;
class ClassLoaderData;

struct LoadedMethodProfile {
    MethodData *method_data;
    MethodCounters *method_counters;
};

template<typename T1, typename T2>
class tagged_ptr_union {
public:

  uintptr_t _ptr_bits;

#define TAG_BIT (1ULL << 50)
  bool flag() const {
    return _ptr_bits & TAG_BIT;
  }

  void set_flag(bool f) {
    if(f)
      _ptr_bits |= TAG_BIT;
    else
      _ptr_bits &= ~TAG_BIT;
  }

public:
    tagged_ptr_union()
     : _ptr_bits(0)
    { }

    bool is_first() const { return !flag(); }
    bool is_second() const { return flag(); }

    T1 *first() const {
      assert(this->is_first(), "Invariant");
      return (T1*)_ptr_bits;
    }

    void set_first(T1 *ptr) {
      _ptr_bits = (uintptr_t)ptr;
      set_flag(false);
    }

    T2 *second() const {
      assert(this->is_second(), "Invariant");
      return (T2*)(_ptr_bits & ~ TAG_BIT);
    }

    void set_second(T2 *ptr) {
      _ptr_bits = (uintptr_t)ptr;
      set_flag(true);
    }

};


class SerializatiedKlassList {

  typedef std::vector<Klass*, malloc_allocator<Klass*> > vector;
  typedef tagged_ptr_union<Klass, vector> Data;
  Data _data;

 public:
  SerializatiedKlassList(Klass *k = NULL) {
    _data.set_first(k);
  }

  void append(Klass *k) {
    if(_data.is_first() && _data.first() == NULL) {
        _data.set_first(k);
    } else if(_data.is_first()) {
        Klass *array[] = { _data.first(), k };
        _data.set_second(new (&nont) vector(array, array + 2));
    } else {
      _data.second()->push_back(k);
    }
  }

  Klass *first() const {
    if(_data.is_first())
      return _data.first();
    return _data.second()->at(0);
  }

  Klass *at(size_t i) const {
    if(_data.is_first()) {
      assert(i == 0 && _data.first() != NULL, "Out of bounds");
      return _data.first();
    }
    return _data.second()->at(i);
  }

  size_t size() const {
    if(_data.is_first()) {
      if(_data.first() == NULL)
        return 0;
      return 1;
    }
    return _data.second()->size();
  }

  static std::map<pstring, SerializatiedKlassList, std::less<pstring>, malloc_allocator<pstring> > klass_name_map;

  static SerializatiedKlassList& klasses_with_name(const pstring &name) {
    return klass_name_map[name];
  }
};

class ProfilingDataSerializer {

  static ProfilingDataSerializer _shared;

  FILE *_file;
  bool _first;

 public:

  ProfilingDataSerializer() : _file(NULL), _first(false) {}

  bool open(const char *fname);
  void close();
  bool is_open() {
    return _file != NULL;
  }

  static ProfilingDataSerializer *shared() {
    return &_shared;
  }
  void serialize_method(Method*);
};

#endif
